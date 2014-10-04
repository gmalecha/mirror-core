Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.

Set Implicit Arguments.
Set Strict Implicit.

Section semantic.
  Variable typ : Type.
  Variable expr : Type.
  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr _ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.

  Context {ExprOk_expr : ExprOk _}.

  Let tvProp := @typ0 _ _ _ Typ0_Prop.

  Definition Provable_val (val : typD tvProp) : Prop :=
    match @typ0_cast _ _ _ _ in _ = t return t with
      | eq_refl => val
    end.

  Definition Provable tus tvs (e : expr) : option (exprT tus tvs Prop) :=
    match exprD' tus tvs e tvProp with
      | None => None
      | Some p => Some (match @typ0_cast _ _ _ _  in _ = t
                              return exprT tus tvs t
                        with
                          | eq_refl => p
                        end)
    end.

  Theorem Provable_weaken
  : forall tus tus' tvs tvs' e eD,
      Provable tus tvs e = Some eD ->
      exists eD',
        Provable (tus ++ tus') (tvs ++ tvs') e = Some eD' /\
        forall us us' vs vs',
          eD us vs <-> eD' (hlist_app us us') (hlist_app vs vs').
  Proof.
    unfold Provable.
    intros; forward; inv_all; subst.
    eapply exprD'_weaken with (tus' := tus') (tvs' := tvs') in H; eauto.
    forward_reason.
    rewrite H. eexists; split; eauto.
    intros.
    autorewrite with eq_rw; simpl.
    rewrite <- H0. reflexivity.
  Qed.

  Definition AllProvable tus tvs (es : list expr)
  : option (exprT tus tvs Prop) :=
    match mapT (T:=list) (F:=option) (Provable tus tvs) es with
      | None => None
      | Some Ps => Some (fun us vs => Forall (fun x => x us vs) Ps)
    end.

  Theorem AllProvable_nil
  : forall tus tvs, exists eD,
      AllProvable tus tvs nil = Some eD /\
      forall us vs, eD us vs.
  Proof.
    compute. intros. eexists; split; auto.
    constructor.
  Qed.

  Theorem AllProvable_nil_Some
  : forall tus tvs eD,
      AllProvable tus tvs nil = Some eD ->
      forall us vs, eD us vs.
  Proof.
    compute. intros; inv_all; subst. constructor.
  Qed.

  Theorem AllProvable_cons
  : forall tus tvs p ps PD,
      AllProvable tus tvs (p :: ps) = Some PD ->
      exists pD psD,
        Provable tus tvs p = Some pD /\
        AllProvable tus tvs ps = Some psD /\
        forall us vs,
          PD us vs <-> (pD us vs /\ psD us vs).
  Proof.
    unfold AllProvable.
    simpl. intros.
    forward. inv_all; subst.
    do 2 eexists; split; eauto.
    split; eauto.
    simpl. intros.
    split.
    { inversion 1; subst; auto. }
    { constructor; intuition. }
  Qed.

  Theorem AllProvable_cons'
  : forall tus tvs p ps pD psD,
      Provable tus tvs p = Some pD ->
      AllProvable tus tvs ps = Some psD ->
      exists PD,
        AllProvable tus tvs (p :: ps) = Some PD /\
        forall us vs,
          PD us vs <-> (pD us vs /\ psD us vs).
  Proof.
    unfold AllProvable.
    simpl. intros.
    forward. eexists; split; eauto.
    simpl; intros.
    inv_all; subst.
    split.
    { inversion 1; subst; intuition. }
    { destruct 1; constructor; auto. }
  Qed.

  Theorem AllProvable_weaken
  : forall tus tus' tvs tvs' ps psD,
      AllProvable tus tvs ps = Some psD ->
      exists psD',
        AllProvable (tus ++ tus') (tvs ++ tvs') ps = Some psD' /\
        forall us us' vs vs',
          psD us vs <-> psD' (HList.hlist_app us us') (HList.hlist_app vs vs').
  Proof.
    induction ps; intros.
    { eexists; split; [ reflexivity | ].
      split; intros.
      { constructor. }
      { eapply AllProvable_nil_Some in H; eassumption. } }
    { eapply AllProvable_cons in H.
      forward_reason.
      eapply Provable_weaken with (tus' := tus') (tvs' := tvs') in H.
      eapply IHps in H0.
      forward_reason.
      eapply AllProvable_cons' in H0; eauto.
      forward_reason.
      eexists; split; eauto.
      intros.
      rewrite H1; clear H1.
      rewrite H3; clear H3.
      rewrite H2; clear H2.
      rewrite H4; clear H4. reflexivity. }
  Qed.

  Theorem AllProvable_app
  : forall tus tvs p ps pD psD,
      AllProvable tus tvs p = Some pD ->
      AllProvable tus tvs ps = Some psD ->
      exists PD,
        AllProvable tus tvs (p ++ ps) = Some PD /\
        forall us vs,
          PD us vs <-> (pD us vs /\ psD us vs).
  Proof.
    intros tus tvs p ps pD psD H H'.
    generalize dependent pD.
    induction p.
    { intros.
      simpl. eexists; split; eauto.
      intuition. eapply AllProvable_nil_Some in H; eauto. }
    { intros.
      eapply AllProvable_cons in H.
      forward_reason.
      eapply IHp in H0.
      forward_reason.
      simpl.
      eapply AllProvable_cons' in H0; eauto.
      forward_reason.
      eexists; split; eauto.
      intros.
      rewrite H3; rewrite H2; rewrite H1.
      intuition. }
  Qed.

End semantic.

Arguments Provable {typ expr RType Expr Typ0} tus tvs e : rename.
Arguments AllProvable {typ expr RType Expr Typ0} tus tvs es : rename.