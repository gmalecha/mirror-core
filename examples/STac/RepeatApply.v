Require Import ExtLib.Data.HList.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.SubstI3.
Require Import MirrorCore.EProver2.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.LemmaApply.
Require Import MirrorCore.Util.Iteration.
Require Import MirrorCore.Subst.FastSubst.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.ExprSubst.
Require Import MirrorCore.Ext.ExprUnifySyntactic3.

Require Import FunctionalExtensionality.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable ts : types.
  Variable func : Type.
  Variable RSym_func : SymI.RSym (typD ts) func.
  Variable RSymOk_func : RSymOk RSym_func.

  (** TODO: This should be generalized **)
  Let Expr_expr := @Expr_expr ts func RSym_func.
  Local Existing Instance Expr_expr.
  Local Existing Instance ExprOk_expr.

  (** TODO: I'm going to need to thread facts for a prover through here **)
  Section Branch.
    Variable subst : Type.

    Inductive Result : Type :=
    | Fail
    | Solve : subst -> Result
    | Progress : expr func -> subst -> list typ -> list typ -> Result.

    Definition branch : Type :=
      expr func -> subst -> list typ -> list typ ->
      Result.
  End Branch.

  Section solve_but_last.
    Variable subst : Type.
    Variable Subst_subst : Subst subst (expr func).
    Variables tus tvs : list typ.
    Variable tac : @EProver typ (expr func).

    Fixpoint solve_all_but_last
             (es : list (expr func))
             (sub : subst)
             (facts : Facts tac) {struct es}
    : Result subst.
    refine match es with
             | nil => Solve sub
             | e :: es =>
               match @Prove _ _ tac subst _ facts tus tvs sub e with
                 | None =>
                   match es with
                     | nil => Progress e sub tus tvs
                     | _ => Fail _
                   end
                 | Some sub' => solve_all_but_last es sub' facts
               end
           end.
    Defined.
  End solve_but_last.

  Section eapply_other.
    Variable subst : Type.
    Variable Subst_subst : Subst subst (expr func).
    Variable SU : SubstUpdate subst (expr func).

    Definition fuel := 100.
    Let eapplicable :=
      @eapplicable typ (expr func) tyProp subst
                   (fun s a e => vars_to_uvars e s a)
                   (fun tus tvs under e1 e2 ty sub =>
                      @exprUnify subst _ _ RSym_func Subst_subst SU fuel
                                 tus tvs under sub e1 e2 ty).

    (** This of this like:
     **   eapply lem ; [ solve [ tac ] | solve [ tac ] | .. | try solve [ tac ] ]
     ** i.e. first eapply the lemma and then require that all side-conditions
     ** except the last are solved by the prover [tac], currently with
     ** empty facts.
     **)
    Definition eapply_other
               (lem : lemma typ (expr func) (expr func))
               (tac : @EProver typ (expr func))
    : branch subst :=
      let len_vars := length lem.(vars) in
      fun e sub tus tvs =>
      match eapplicable sub tus tvs lem e with
        | None => Fail _
        | Some sub' =>
          let premises := nil in
          let facts := Summarize _ (tus ++ lem.(vars)) tvs nil in
          match
            solve_all_but_last _ (tus ++ lem.(vars)) tvs tac
                               premises sub'
                               facts
          with
            | Fail => Fail _
            | Solve sub'' =>
              let from := length tus in
              match pull (expr := expr func) from len_vars sub'' with
                | None => Fail _
                | Some sub''' => Solve sub'''
              end
            | Progress e sub'' tus tvs =>
              let from := length tus in
              match pull (expr := expr _) from len_vars sub'' with
                | None => Fail _
                | Some sub''' => Progress e sub''' tus tvs
              end
          end
      end.
  End eapply_other.

  Section first_branch.
    Variable subst : Type.

    Definition FIRST (brs : list (branch subst)) : branch subst :=
      fun e sub tus tvs =>
        (fix FIRST (brs : list (branch subst)) : Result subst :=
           match brs with
             | nil => Fail _
             | br :: brs =>
               match br e sub tus tvs with
                 | Fail => FIRST brs
                 | x => x
               end
           end) brs.
  End first_branch.

  Section repeat_branch.
    Variable subst : Type.

    Definition REPEAT (max : nat) (br : branch subst) : branch subst :=
      (fix DO (n : nat) : branch subst :=
         match n with
           | 0 => @Progress _
           | S n =>
             fun e sub tus tvs =>
               match br e sub tus tvs with
                 | Fail => Progress e sub tus tvs (** Never fails **)
                 | Progress e sub tus tvs => DO n e sub tus tvs
                 | Solve s => Solve s
               end
         end) max.
  End repeat_branch.

  Section try_branch.
    Variable subst : Type.

    Definition TRY (b : branch subst) : branch subst :=
      fun e sub tus tvs =>
        match b e sub tus tvs with
          | Fail => Progress e sub tus tvs
          | x => x
        end.
  End try_branch.

End parameterized.
