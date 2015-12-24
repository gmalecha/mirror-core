(** Basic Rtac tactics specialized for the lambda language.
 **)
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprUnify.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.RTac.RTac.

Set Implicit Arguments.
Set Strict Implicit.

Section tactics.
  Variables typ func : Type.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Typ0_Prop : Typ0 RType_typ Prop}.
  Context {Typ2_func : Typ2 RType_typ RFun}.
  Context {Typ2Ok_func : Typ2Ok Typ2_func}.
  Context {RSym_sym : RSym func}.
  Context {RSymOk_sym : RSymOk RSym_sym}.
  Let Expr_expr : Expr typ (expr typ func) := Expr_expr.
  Local Existing Instance Expr_expr.
  Let ExprOk_expr : ExprOk Expr_expr := ExprOk_expr.
  Local Existing Instance ExprOk_expr.

  (* Apply Tactics *)
  Definition EAPPLY_depth (depth : nat)
  : Lemma.lemma typ (expr typ func) (expr typ func) ->
    rtac typ (expr typ func) :=
    EAPPLY (fun subst Ssubst SUsubst => exprUnify depth).
  Definition APPLY_depth (depth : nat)
  : Lemma.lemma typ (expr typ func) (expr typ func) ->
    rtac typ (expr typ func) :=
    APPLY (fun subst Ssubst SUsubst => exprUnify depth).

  Definition EAPPLY (l : Lemma.lemma typ (expr typ func) (expr typ func))
  : rtac typ (expr typ func) :=
    EAPPLY_depth (S (length l.(Lemma.vars))) l.

  Definition APPLY (l : Lemma.lemma typ (expr typ func) (expr typ func))
  : rtac typ (expr typ func) :=
    APPLY_depth (S (length l.(Lemma.vars))) l.

  Global Instance RtacSound_EAPPLY_depth depth l (RL : ReifiedLemma l)
  : RtacSound (EAPPLY_depth depth l).
  Proof.
    constructor.
    eapply EAPPLY_sound; eauto with typeclass_instances.
    intros. eapply exprUnify_sound; eauto with typeclass_instances.
  Qed.

  Global Instance RtacSound_APPLY_depth depth l (RL : ReifiedLemma l)
  : RtacSound (APPLY_depth depth l).
  Proof.
    constructor.
    eapply APPLY_sound; eauto with typeclass_instances.
    intros. eapply exprUnify_sound; eauto with typeclass_instances.
  Qed.

  Global Instance RtacSound_EAPPLY l (RL : ReifiedLemma l)
  : RtacSound (EAPPLY l).
  Proof.
    eapply RtacSound_EAPPLY_depth; assumption.
  Qed.

  Global Instance RtacSound_APPLY l (RL : ReifiedLemma l)
  : RtacSound (APPLY l).
  Proof.
    eapply RtacSound_APPLY_depth; assumption.
  Qed.

  (* * Apply tactics with minification *)
  Definition EAPPLY_m (l : Lemma.lemma typ (expr typ func) (expr typ func))
  : rtac typ (expr typ func) :=
    THEN (EAPPLY_depth (S (length l.(Lemma.vars))) l)
         (@MINIFY _ _ _ _ _).

  Definition APPLY_m (l : Lemma.lemma typ (expr typ func) (expr typ func))
  : rtac typ (expr typ func) :=
    THEN (APPLY_depth (S (length l.(Lemma.vars))) l)
         (@MINIFY _ _ _ _ _).

  Global Instance RtacSound_EAPPLY_m l (RL : ReifiedLemma l)
  : RtacSound (EAPPLY_m l).
  Proof.
    constructor.
    eapply THEN_sound.
    - eapply RtacSound_proof. eauto with typeclass_instances.
    - eapply MINIFY_sound; eauto with typeclass_instances.
  Qed.

  Global Instance RtacSound_APPLY_m l (RL : ReifiedLemma l)
  : RtacSound (APPLY_m l).
  Proof.
    constructor.
    eapply THEN_sound.
    - eapply RtacSound_proof. eauto with typeclass_instances.
    - eapply MINIFY_sound; eauto with typeclass_instances.
  Qed.

  (* Assumption Tactics *)
  Definition EASSUMPTION : rtac typ (expr typ func) :=
    @EASSUMPTION typ (expr typ func) _ _
       (fun subst S_subst SU ctx e1 e2 s =>
          @exprUnify subst typ func _ _ _ S_subst SU 30
                     (getUVars ctx) (getVars ctx) 0 e1 e2 (typ0 (F:=Prop)) s).

  Global Instance RtacSound_EASSUMPTION : RtacSound EASSUMPTION.
  Proof.
    constructor.
    eapply Assumption.ASSUMPTION_sound.
    generalize 30.
    intros.
    destruct (@exprUnify_sound (ctx_subst ctx) typ func _ _ _ _ _ _ _ _ _ _ n
               _ _ _ _ _ _ _ nil H H0).
    split; auto.
    simpl in *.
    intros.
    unfold Ctx.propD, exprD'_typ0 in *.
    forwardy. inv_all; subst.
    unfold exprD', tus, tvs in *. simpl in *.
    destruct (@H2 _ _ sD H3 H4 H5); clear H2.
    forward_reason.
    split; eauto.
    eexists; split; eauto.
    intros.
    specialize (H7 _ _ H8).
    destruct H7.
    split; auto.
    specialize (H9 HList.Hnil); simpl in H9.
    clear - H9.
    generalize (typ0_cast (F:=Prop)).
    generalize dependent (typD (typ0 (F:=Prop))).
    intros; subst. assumption.
  Defined.

  (* Simplification Tactics *)
  Definition SIMPL (fr : full_reducer typ func) : rtac typ (expr typ func) :=
    SIMPLIFY (fun Tsubst Csubst ctx subst e => fr nil e nil).

  Global Instance RtacSound_SIMPL (fr : full_reducer typ func)
         (frOk : full_reducer_ok fr)
  : RtacSound (SIMPL fr).
  Proof.
    unfold SIMPL.
    constructor.
    eapply SIMPLIFY_sound.
    intros.
    unfold Ctx.propD, exprD'_typ0 in H3.
    forwardy.
    inv_all.
    edestruct (fun H =>
                 frOk e nil (getUVars ctx) (getVars ctx)
                      (getUVars ctx) (getVars ctx)
                      (fun us vs => fun us' vs' => us = us' /\ vs = vs')
                      H
              nil (@typ0 _ _ Prop _) nil).
    - constructor. intuition.
    - simpl. eapply H3.
    - reflexivity.
    - subst.
      destruct H5.
      unfold Ctx.propD, exprD'_typ0.
      change_rewrite H.
      eexists; split; [ reflexivity | ].
      simpl in *.
      eapply Pure_pctxD; eauto.
      intros. specialize (H4 us vs us vs (conj eq_refl eq_refl)).
      generalize dependent (typ0_cast (F:=Prop)).
      clear - H4.
      generalize dependent (typD (typ0 (F:=Prop))).
      intros; subst.
      rewrite H4. assumption.
  Qed.

  Definition INTRO_ptrn (p : ptrn (expr typ func) (OpenAs typ (expr typ func)))
  : rtac typ (expr typ func) :=
    INTRO (fun e => run_tptrn (pdefault (pmap Some p) None) e).

  Definition open_ptrn_sound (p : ptrn (expr typ func) (OpenAs typ (expr typ func))) : Prop :=
    forall (tus tvs : list typ) (e : expr typ func) (ot : OpenAs typ (expr typ func)),
      Succeeds e p ot ->
      match ot with
      | AsEx t gl' =>
        forall (eD : exprT tus tvs Prop) (e' : expr typ func)
               (e'D : exprT (tus ++ t :: nil) tvs (typD t)),
          Ctx.propD tus tvs e = Some eD ->
          exprD' (tus ++ t :: nil) tvs e' t = Some e'D ->
          exists eD' : exprT (tus ++ t :: nil) tvs Prop,
            Ctx.propD (tus ++ t :: nil) tvs (gl' e') = Some eD' /\
            (forall (us : HList.hlist typD tus) (vs : HList.hlist typD tvs),
                (exists x : typD t,
                    eD'
                      (HList.hlist_app us
                                       (HList.Hcons
                                          (e'D (HList.hlist_app us (HList.Hcons x HList.Hnil)) vs)
                                          HList.Hnil)) vs) -> eD us vs)
      | AsAl t gl' =>
        forall (eD : exprT tus tvs Prop) (e' : expr typ func)
               (e'D : exprT tus (tvs ++ t :: nil) (typD t)),
          Ctx.propD tus tvs e = Some eD ->
          exprD' tus (tvs ++ t :: nil) e' t = Some e'D ->
          exists eD' : exprT tus (tvs ++ t :: nil) Prop,
            Ctx.propD tus (tvs ++ t :: nil) (gl' e') = Some eD' /\
            (forall (us : HList.hlist typD tus) (vs : HList.hlist typD tvs),
                (forall x : typD t,
                    eD' us
                        (HList.hlist_app vs
                                         (HList.Hcons
                                            (e'D us (HList.hlist_app vs (HList.Hcons x HList.Hnil)))
                                            HList.Hnil))) -> eD us vs)
      | AsHy h gl' =>
        forall eD : exprT tus tvs Prop,
          Ctx.propD tus tvs e = Some eD ->
          exists eD' hD : exprT tus tvs Prop,
            Ctx.propD tus tvs h = Some hD /\
            Ctx.propD tus tvs gl' = Some eD' /\
            (forall (us : HList.hlist typD tus) (vs : HList.hlist typD tvs),
                (hD us vs -> eD' us vs) -> eD us vs)
      end.

  Definition INTRO_ptrn_sound : forall p,
      ptrn_ok p ->
      open_ptrn_sound p ->
      rtac_sound (INTRO_ptrn p).
  Proof.
    intros.
    apply INTRO_sound.
    red. intros. eapply H0; clear H0.
    revert H1.
    unfold run_tptrn.
    eapply pdefault_sound.
    - eapply ptrn_ok_pmap. eassumption.
    - red. red. red. intros.
      subst. red in H1. red in H1.
      split.
      + intros.
        eapply H0. erewrite H1. eassumption.
        compute; auto.
      + intros.
        eapply H0. erewrite <- H1. eassumption.
        compute; auto.
    - intros.
      eapply Succeeds_pmap in H0; eauto.
      destruct H0. destruct H0.
      subst. unfold ptret in H1. inv_all.
      subst. assumption.
    - unfold ptret. inversion 1.
  Qed.

End tactics.