Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SubstI.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Context {typ expr : Type}.
  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr RType_typ expr}.
  Variable T : Type.
  Context {Typ0_T : Typ0 _ T}.

  Definition exprD'_typ0 tus (tvs : list typ) (goal : expr)
  : option (exprT tus tvs T) :=
    match exprD' tus tvs goal (@typ0 _ _ _ _) return option (exprT tus tvs T) with
      | None => None
      | Some val =>
        Some match typ0_cast(F:=T) in _ = T return exprT tus tvs T with
               | eq_refl => val
             end
    end.

  Lemma exprD'_typ0_conv
  : forall tus tus' (tvs tvs' : list typ) (pfu : tus' = tus) (pfv : tvs' = tvs),
      exprD'_typ0 tus tvs =
      match pfu in _ = tu , pfv in _ = tv
            return expr -> option (exprT tu tv T)
      with
        | eq_refl , eq_refl => exprD'_typ0 tus' tvs'
      end.
  Proof.
    destruct pfu; destruct pfv. reflexivity.
  Qed.

  Lemma exprD'_typ0_weaken (ExprOk_expr : ExprOk _)
  : forall tus (tvs : tenv typ) tus' (tvs' : list typ) (l0 : expr)
           (lD : exprT tus tvs T),
      exprD'_typ0 tus tvs l0 = Some lD ->
      exists
        lD' : exprT (tus ++ tus') (tvs ++ tvs') T,
        exprD'_typ0 (tus ++ tus') (tvs ++ tvs') l0 = Some lD' /\
        (forall (us : hlist _ tus) (vs : hlist typD tvs)
                (us' : hlist _ tus') (vs' : hlist typD tvs'),
           lD us vs = lD' (hlist_app us us') (hlist_app vs vs')).
  Proof.
    unfold exprD'_typ0.
    intros. forward. inv_all; subst.
    eapply exprD'_weaken with (tus' := tus') (tvs' := tvs') in H; eauto.
    forward_reason. rewrite H.
    eexists; split; eauto. intros.
    unfold exprT, OpenT.OpenT.
    autorewrite with eq_rw.
    rewrite <- H0.
    reflexivity.
  Qed.

  Definition exprD'_typ0_weakenU (ExprOk_expr : ExprOk _)
  : forall tus (tvs : tenv typ) tus' (l0 : expr)
           (lD : exprT tus tvs T),
      exprD'_typ0 tus tvs l0 = Some lD ->
      exists
        lD' : exprT (tus ++ tus') tvs T,
        exprD'_typ0 (tus ++ tus') tvs l0 = Some lD' /\
        (forall (us : hlist _ tus) (us' : hlist _ tus')
                (vs : hlist typD tvs),
           lD us vs = lD' (hlist_app us us') vs).
  Proof.
    unfold exprD'_typ0. intros.
    forwardy.
    inv_all; subst.
    apply exprD'_weakenU with (tus' := tus') in H; eauto.
    forward_reason.
    rewrite H.
    eexists; split; eauto.
    intros. unfold exprT, OpenT.OpenT.
    autorewrite with eq_rw.
    erewrite H0. reflexivity.
  Qed.

  Definition exprD'_typ0_weakenV (ExprOk_expr : ExprOk _)
  : forall tus (tvs : tenv typ) tvs' (l0 : expr)
           (lD : exprT tus tvs T),
      exprD'_typ0 tus tvs l0 = Some lD ->
      exists
        lD' : exprT tus (tvs ++ tvs') T,
        exprD'_typ0 tus (tvs ++ tvs') l0 = Some lD' /\
        (forall (us : hlist _ tus) (vs : hlist typD tvs)
                (vs' : hlist typD tvs'),
           lD us vs = lD' us (hlist_app vs vs')).
  Proof.
    unfold exprD'_typ0. intros.
    forwardy.
    inv_all; subst.
    apply exprD'_weakenV with (tvs' := tvs') in H; eauto.
    forward_reason.
    rewrite H.
    eexists; split; eauto.
    intros. unfold exprT,OpenT.OpenT.
    autorewrite with eq_rw.
    erewrite H0. reflexivity.
  Qed.

End parameterized.

Arguments exprD'_typ0 {_ _ _ _} T {_} _ _ _ : rename.