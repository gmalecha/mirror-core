Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.ExprI.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Context {typ expr : Set}.
  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr typ expr}.
  Variable T : Type.
  Context {Typ0_T : Typ0 _ T}.

  Definition exprD_typ0 (tus tvs : list typ) (goal : expr)
  : option (exprT tus tvs T) :=
    match exprD tus tvs (@typ0 _ _ _ _) goal
          return option (exprT tus tvs T)
    with
    | None => None
    | Some val =>
      Some match typ0_cast(F:=T) in _ = T return exprT tus tvs T with
           | eq_refl => val
           end
    end.

  Lemma exprD_typ0_conv
  : forall (tus tvs tus' tvs' : list typ) (pfu : tus' = tus) (pfv : tvs' = tvs),
      exprD_typ0 tus tvs =
      match pfu in _ = tu , pfv in _ = tv
            return expr -> option (exprT tu tv T)
      with
      | eq_refl , eq_refl => exprD_typ0 tus' tvs'
      end.
  Proof.
    destruct pfu; destruct pfv. reflexivity.
  Qed.

  Lemma exprD_typ0_weaken (ExprOk_expr : ExprOk _)
  : forall (tus tvs tus' tvs' : tenv typ) (l0 : expr)
           (lD : exprT tus tvs T),
      exprD_typ0 tus tvs l0 = Some lD ->
      exists
        lD' : exprT (tus ++ tus') (tvs ++ tvs') T,
        exprD_typ0 (tus ++ tus') (tvs ++ tvs') l0 = Some lD' /\
        (forall (us : hlist typD tus) (vs : hlist typD tvs)
                (us' : hlist typD tus') (vs' : hlist typD tvs'),
           lD us vs = lD' (hlist_app us us') (hlist_app vs vs')).
  Proof.
    unfold exprD_typ0.
    intros. forward. inv_all; subst.
    eapply exprD_weaken with (tus' := tus') (tvs' := tvs') in H; eauto.
    forward_reason. rewrite H.
    eexists; split; eauto. intros.
    autorewrite with eq_rw; simpl.
    rewrite <- H0.
    reflexivity.
  Qed.

  Definition exprD_typ0_weakenU (ExprOk_expr : ExprOk _)
  : forall (tus tvs tus' : tenv typ) (l0 : expr)
           (lD : hlist typD tus -> hlist typD tvs -> T),
      exprD_typ0 tus tvs l0 = Some lD ->
      exists
        lD' : hlist typD (tus ++ tus') -> hlist typD tvs -> T,
        exprD_typ0 (tus ++ tus') tvs l0 = Some lD' /\
        (forall (us : hlist typD tus) (us' : hlist typD tus')
                (vs : hlist typD tvs),
           lD us vs = lD' (hlist_app us us') vs).
  Proof.
    unfold exprD_typ0. intros.
    forwardy.
    inv_all; subst.
    apply exprD_weakenU with (tus' := tus') in H; eauto.
    forward_reason.
    rewrite H.
    eexists; split; eauto.
    intros.
    autorewrite with eq_rw; simpl.
    erewrite H0. reflexivity.
  Qed.

  Definition exprD_typ0_weakenV (ExprOk_expr : ExprOk _)
  : forall (tus tvs tvs' : tenv typ) (l0 : expr)
           (lD : hlist typD tus -> hlist typD tvs -> T),
      exprD_typ0 tus tvs l0 = Some lD ->
      exists
        lD' : hlist typD tus -> hlist typD (tvs ++ tvs') -> T,
        exprD_typ0 tus (tvs ++ tvs') l0 = Some lD' /\
        (forall (us : hlist typD tus) (vs : hlist typD tvs)
                (vs' : hlist typD tvs'),
           lD us vs = lD' us (hlist_app vs vs')).
  Proof.
    unfold exprD_typ0. intros.
    forwardy.
    inv_all; subst.
    apply exprD_weakenV with (tvs' := tvs') in H; eauto.
    forward_reason.
    rewrite H.
    eexists; split; eauto.
    intros.
    autorewrite with eq_rw.
    erewrite H0. reflexivity.
  Qed.

End parameterized.

Arguments exprD_typ0_weakenU {_ _ _ _ _ _ _ tus tvs} tus' {_ _} _ : rename.
Arguments exprD_typ0_weakenV {_ _ _ _ _ _ _ tus tvs} tvs' {_ _} _ : rename.
Arguments exprD_typ0_weaken {_ _ _ _ _ _ _ tus tvs} tus' tvs' {_ _} _ : rename.
