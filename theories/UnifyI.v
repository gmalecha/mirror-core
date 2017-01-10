Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Map.FMapPositive.

Require Import MirrorCore.ExprI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.SymI.

Set Implicit Arguments.
Set Strict Implicit.

Section with_Expr.
  Variable typ : Set.
  Variable expr : Set.
  Variable subst : Type.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Expr_expr : @Expr typ _ expr}.
  Context {Subst_subst : Subst subst expr}.
  Context {SubstOk_subst : SubstOk subst typ expr}.
  Context {SubstUpdate_subst : SubstUpdate subst expr}.
  Context {SubstUpdateOk_subst : SubstUpdateOk subst typ expr}.

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
        exprD tu (tv' ++ tv) t e1 = Some v1 ->
        exprD tu (tv' ++ tv) t e2 = Some v2 ->
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

Section with_RSym.
  Variable typ func : Set.
  Context {RType_typ : RType typ}.
  Context {RSym_func : RSym func}.

  Definition sym_unify (a b : func) (s : FMapPositive.pmap typ) : 
    option (FMapPositive.pmap typ) :=
    match sym_eqb a b with
    | Some true => Some s
    | _ => None
    end.

End with_RSym.
