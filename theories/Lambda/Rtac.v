(** Basics Rtac tactics specialized for the lambda language.
 **)
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.Forwardy.
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
End tactics.