Require Import ExtLib.Data.HList.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SubstI.

Set Implicit Arguments.
Set Strict Implicit.

Section with_Expr.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Expr_expr : @Expr typ _ expr}.
  Context {Subst_subst : Subst subst expr}.
  Context {SubstOk_subst : SubstOk Subst_subst}.
  Context {SubstUpdate_subst : SubstUpdate subst expr}.
  Context {SubstUpdateOk_subst : SubstUpdateOk SubstUpdate_subst _}.

  Local Existing Instance RType_typ.
  Local Existing Instance Expr_expr.

  Definition unifier : Type :=
    forall (tus tvs : tenv typ) (under : nat) (l r : expr)
           (t : typ) (s : subst), option subst.

  Variable unify : unifier.

  Definition unify_sound : Prop :=
    forall (tu tv : tenv typ) (e1 e2 : expr) (s s' : subst)
           (t : typ) (tv' : tenv typ),
      unify tu (tv' ++ tv) (length tv') e1 e2 t s = Some s' ->
      WellFormed_subst s ->
      WellFormed_subst s' /\
      forall v1 v2 sD,
        exprD' tu (tv' ++ tv) e1 t = Some v1 ->
        exprD' tu (tv' ++ tv) e2 t = Some v2 ->
        substD tu tv s = Some sD ->
        exists sD',
             substR tu tv s s'
          /\ substD tu tv s' = Some sD'
          /\ forall us vs,
               sD' us vs ->
               sD us vs /\
               forall vs',
                 v1 us (hlist_app vs' vs) = v2 us (hlist_app vs' vs).

End with_Expr.
