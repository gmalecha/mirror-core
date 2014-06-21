Require Import ExtLib.Data.HList.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.SubstI3.
Require Import MirrorCore.EProver2.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.LemmaApply.
Require Import MirrorCore.STac.Core.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.
  Variable tyProp : typ.

  Variable vars_to_uvars : nat -> nat -> expr -> expr.
  Variable exprUnify : tenv typ -> tenv typ -> nat -> expr -> expr -> typ -> subst -> option subst.
  Variable instantiate : (nat -> option expr) -> nat -> expr -> expr.

  Section solve_but_last.
    Variable Subst_subst : Subst subst expr.
    Variables tus tvs : list typ.
    Variable tac : stac typ expr subst.

    Fixpoint solve_all_but_last
             (es : list expr)
             (sub : subst) {struct es}
    : Result typ expr subst.
    refine match es with
             | nil => @Solve _ _ _ sub
             | e :: es =>
               let e := instantiate (fun u => lookup u sub) 0 e in
               match tac e sub tus tvs with
                 | Solve sub' => solve_all_but_last es sub'
                 | Progress e sub tus tvs =>
                   match es with
                     | nil => Progress e sub tus tvs
                     | _ => @Fail _ _ _
                   end
                 | Fail => @Fail _ _ _
               end
           end.
    Defined.
  End solve_but_last.

  Section eapply_other.
    Variable Subst_subst : Subst subst expr.
    Variable SU : SubstUpdate subst expr.

    Definition fuel := 100.
    Let eapplicable :=
      @eapplicable typ expr tyProp subst vars_to_uvars
                   exprUnify.

    (** This of this like:
     **   eapply lem ; [ solve [ tac ] | solve [ tac ] | .. | try solve [ tac ] ]
     ** i.e. first eapply the lemma and then require that all side-conditions
     ** except the last are solved by the prover [tac], currently with
     ** empty facts.
     **)
    Definition eapply_other
               (lem : lemma typ expr expr)
               (tac : stac typ expr subst)
    : stac typ expr subst :=
      let len_vars := length lem.(vars) in
      fun e sub tus tvs =>
      match eapplicable sub tus tvs lem e with
        | None => @Fail _ _ _
        | Some sub' =>
          let len_uvars := length tus in
          let premises := map (vars_to_uvars 0 len_uvars) lem.(premises) in
          match
            solve_all_but_last _ (tus ++ lem.(vars)) tvs tac
                               premises sub'
          with
            | Fail => @Fail _ _ _
            | Solve sub'' =>
              match pull (expr := expr) len_uvars len_vars sub'' with
                | None => @Fail _ _ _
                | Some sub''' => @Solve _ _ _ sub'''
              end
            | Progress e sub'' tus tvs =>
              (** TODO: In this case it is not necessary to pull everything
               ** I could leave unification variables in place
               **)
              match pull (expr := expr) len_uvars len_vars sub'' with
                | None => @Fail _ _ _
                | Some sub''' => Progress e sub''' (firstn len_uvars tus) tvs
              end
          end
      end.
  End eapply_other.

End parameterized.
