Require Import MirrorCore.ExprI.
Require Import MirrorCore.Subst.
Require Import MirrorCore.Prover.

Set Implicit Arguments.
Set Strict Implicit.

Section typed.
  Variables typ expr uvar : Type.

  Variable typD : list Type -> typ -> Type.
  Context {Expr_expr : @Expr typ typD expr}.

  Definition unifier : Type :=
    forall (S : Type) (Subst_S : Subst S expr uvar) (P : @ProverT typ expr),
      Facts P ->
      S -> expr -> expr -> option S.

(*
Definition unifier_WellTyped (ts : types) (fs : tfunctions) (unify : unifier ts) : Prop :=
  forall  (S : Type) (Subst_S : Subst ts S) (P : ProverT ts)
    (F : Facts P) (subst : S) (e1 e2 : expr ts) subst',
    unify _ _ P F subst e1 e2 = Some subst' ->
    forall (uenv venv : tenv) (t : typ),
      WellTyped_expr fs uenv venv e1 t ->
      WellTyped_expr fs uenv venv e2 t ->
(*
      WellTyped_Subst fs uenv venv subst ->
      WellTyped_Subst fs uenv venv subst'.
*)
      True.
*)

  Definition unifier_sound (unify : unifier) : Prop :=
    forall (S : Type) (Subst_S : Subst S expr uvar)
           (P : ProverT expr) (*PC : ProverT_correct P fs*)
           (F : Facts P) (subst : S) (e1 e2 : expr) subst',
      unify _ _ P F subst e1 e2 = Some subst' ->
      forall us vs t,
        exprD us vs e1 t = exprD us vs e2 t.
