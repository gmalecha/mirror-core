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

  Section solve_but_last.
    Variable Subst_subst : Subst subst expr.
    Variables tus tvs : list typ.
    Variable tac : @EProver typ expr.

    Fixpoint solve_all_but_last
             (es : list expr)
             (sub : subst)
             (facts : Facts tac) {struct es}
    : Result typ expr subst.
    refine match es with
             | nil => @Solve _ _ _ sub
             | e :: es =>
               match @Prove _ _ tac subst _ facts tus tvs sub e with
                 | None =>
                   match es with
                     | nil => Progress e sub tus tvs
                     | _ => @Fail _ _ _
                   end
                 | Some sub' => solve_all_but_last es sub' facts
               end
           end.
    Defined.
  End solve_but_last.

  Variable vars_to_uvars : nat -> nat -> expr -> expr.
  Variable exprUnify : tenv typ -> tenv typ -> nat -> expr -> expr -> typ -> subst -> option subst.

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
               (tac : @EProver typ expr)
    : stac typ expr subst :=
      let len_vars := length lem.(vars) in
      fun e sub tus tvs =>
      match eapplicable sub tus tvs lem e with
        | None => @Fail _ _ _
        | Some sub' =>
          let premises := nil in
          let facts := Summarize _ (tus ++ lem.(vars)) tvs nil in
          match
            solve_all_but_last _ (tus ++ lem.(vars)) tvs tac
                               premises sub'
                               facts
          with
            | Fail => @Fail _ _ _
            | Solve sub'' =>
              let from := length tus in
              match pull (expr := expr) from len_vars sub'' with
                | None => @Fail _ _ _
                | Some sub''' => @Solve _ _ _ sub'''
              end
            | Progress e sub'' tus tvs =>
              let from := length tus in
              match pull (expr := expr) from len_vars sub'' with
                | None => @Fail _ _ _
                | Some sub''' => Progress e sub''' tus tvs
              end
          end
      end.
  End eapply_other.

End parameterized.
