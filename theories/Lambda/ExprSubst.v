(** This file contains generic functions for manipulating,
 ** (i.e. substituting and finding) unification variables
 **)
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Data.Bool.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.VariablesI.
Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.Lambda.ExprD.
Require Import MirrorCore.Lambda.ExprLift.

Set Implicit Arguments.
Set Strict Implicit.

Require Import FunctionalExtensionality.

Section mentionsU.
  Variable typ : Type.
  Variable func : Type.

  Lemma mentionsU_lift
  : forall u e a b,
      _mentionsU u (lift (typ := typ) (func := func) a b e) = _mentionsU u e.
  Proof.
    induction e; simpl; intros; intuition;
    Cases.rewrite_all_goal; intuition.
  Qed.

End mentionsU.

Section instantiate.
  Variable typ : Type.
  Variable func : Type.
  Variable lookup : uvar -> option (expr typ func).

  Fixpoint instantiate (under : nat) (e : expr typ func) : expr typ func :=
    match e with
      | Var _
      | Inj _ => e
      | App l r => App (instantiate under l) (instantiate under r)
      | Abs t e => Abs t (instantiate (S under) e)
      | UVar u =>
        match lookup u with
          | None => UVar u
          | Some e => lift 0 under e
        end
    end.

  Definition instantiates (u : uvar) : Prop :=
    lookup u <> None /\
    forall u' e, lookup u' = Some e ->
                 _mentionsU u e = false.

  Lemma instantiate_instantiates
  : forall u,
      instantiates u ->
      forall e under,
        _mentionsU u (instantiate under e) = false.
  Proof.
    induction e; simpl; intros; auto.
    { rewrite IHe1. auto. }
    { destruct H.
      consider (u ?[ eq ] u0).
      { intros; subst.
        specialize (H0 u0).
        destruct (lookup u0).
        { rewrite mentionsU_lift. auto. }
        { congruence. } }
      { intros.
        consider (lookup u0); intros.
        { rewrite mentionsU_lift. eauto. }
        { simpl. consider (EqNat.beq_nat u u0); try congruence. } } }
  Qed.

End instantiate.

Section instantiate_thm.
  Variable typ : Type.
  Variable func : Type.
  Variable RType_typ : RType typ.
  Variable Typ2_Fun : Typ2 _ Fun.
  Context {RSym_func : RSym func}.

  (** Reasoning principles **)
  Context {RTypeOk_typD : RTypeOk}.
  Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.
  Context {RSymOk_func : RSymOk RSym_func}.

  Let Expr_expr := @Expr_expr _ _ RType_typ _ _.
  Local Existing Instance Expr_expr.

  Lemma typeof_expr_instantiate
  : forall f tus tvs,
      (forall u e, f u = Some e ->
                   typeof_expr tus tvs e = nth_error tus u) ->
      forall e tvs',
        typeof_expr tus (tvs' ++ tvs) e =
        typeof_expr tus (tvs' ++ tvs) (instantiate f (length tvs') e).
  Proof.
    induction e; simpl; intros; auto.
    { rewrite (IHe1 tvs').
      rewrite (IHe2 tvs').
      reflexivity. }
    { specialize (IHe (t :: tvs')).
      simpl in IHe.
      rewrite IHe. reflexivity. }
    { specialize (H u).
      destruct (f u).
      { specialize (typeof_expr_lift tus e nil tvs' tvs).
        simpl.
        intro XXX; change_rewrite XXX; clear XXX.
        symmetry. eapply H; reflexivity. }
      { reflexivity. } }
  Qed.

  Lemma typeof_expr_instantiate'
  : forall f tus tvs,
      (forall u e t, f u = Some e ->
                     nth_error tus u = Some t ->
                     typeof_expr tus tvs e = Some t) ->
      forall e tvs' t,
        typeof_expr tus (tvs' ++ tvs) e = Some t ->
        typeof_expr tus (tvs' ++ tvs) (instantiate f (length tvs') e) = Some t.
  Proof.
    induction e; simpl; intros; auto.
    { forwardy.
      erewrite IHe1 by eassumption.
      erewrite IHe2 by eassumption.
      eassumption. }
    { specialize (IHe (t :: tvs')).
      simpl in IHe.
      forwardy.
      erewrite IHe by eassumption. eassumption. }
    { specialize (H u).
      destruct (f u).
      { specialize (typeof_expr_lift tus e nil tvs' tvs).
        simpl.
        intro XXX; change_rewrite XXX; clear XXX.
        eapply H; eauto. }
      { eapply H0. } }
  Qed.

  Theorem exprD'_instantiate_ho
  : instantiate_spec_ho (@instantiate typ func).
  Proof.
    red. unfold ExprI.exprD'; simpl.
    induction e; simpl; intros.
    { eexists; split; eauto.
      eapply CtxLogic.exprTPure; eauto. }
    { eexists; split; eauto.
      eapply CtxLogic.exprTPure; eauto. }
    { autorewrite with exprD_rw in *; eauto.
      simpl in *.
      forwardy.
      eapply typeof_expr_instantiate' with (f := f) in H0.
      change_rewrite H0.
      specialize (IHe1 tvs' (typ2 y t) _ _ EApp H H1).
      specialize (IHe2 _ _ _ _ EApp H H2).
      forward_reason.
      change_rewrite H5. change_rewrite H4.
      eexists; split; [ reflexivity | ].
      intros. inv_all; subst.
      unfold exprT_App.
      autorewrite with eq_rw.
      revert H6. eapply CtxLogic.exprTAp.
      revert H7. eapply CtxLogic.exprTAp.
      eapply CtxLogic.exprTPure.
      clear. intros.
      rewrite H by assumption.
      rewrite H0 by assumption. reflexivity.
      clear - H RTypeOk_typD Typ2Ok_Fun RSymOk_func.
      red in H.
      intros.
      specialize (fun t get => H u e t get H0).
      simpl in *.
      consider (nth_error_get_hlist_nth typD tus u).
      { intros. destruct s.
        specialize (H2 _ _ eq_refl).
        forward_reason.
        eapply nth_error_get_hlist_nth_Some in H.
        simpl in H. forward_reason.
        rewrite x1 in H1. inv_all; subst.
        eapply exprD'_typeof_expr; eauto. }
      { intro. exfalso.
        eapply nth_error_get_hlist_nth_None in H. congruence. } }
    { autorewrite with exprD_rw in *.
      destruct (typ2_match_case t0) as [ [ ? [ ? [ ? ? ] ] ] | ? ].
      { rewrite H1 in *. clear H1.
        simpl in *.
        unfold Relim in *.
        autorewrite with eq_rw in *.
        forwardy.
        Cases.rewrite_all_goal.
        specialize (IHe (t :: tvs')_ _ _ _ H H3).
        forward_reason.
        simpl in *.
        Cases.rewrite_all_goal.
        eexists; split; eauto.
        intros.
        inv_all; subst.
        revert H6. eapply CtxLogic.exprTAp.
        eapply CtxLogic.exprTPure.
        autorewrite with eq_rw.
        intros.
        eapply match_eq_match_eq.
        eapply match_eq_match_eq with (F := fun x => x).
        apply functional_extensionality.
        intro. eapply (H1 (Hcons (Rcast_val y1 x3) vs')); auto. }
      { rewrite H1 in H0. exfalso. congruence. } }
    { red in H.
      specialize (H u).
      destruct (f u).
      { autorewrite with exprD_rw in *; simpl in *.
        forwardy.
        specialize (H _ _ _ eq_refl H0).
        forward_reason.
        generalize (exprD'_lift tus e nil tvs' tvs t).
        destruct y.
        simpl. change_rewrite H.
        intros; forwardy.
        eexists; split; [ eassumption | ].
        intros.
        inv_all; subst.
        revert H3. eapply CtxLogic.exprTAp.
        eapply CtxLogic.exprTPure. intros.
        erewrite H2 by eauto. eapply (H5 us Hnil vs' vs). }
      { clear H.
        eexists; split; [ eassumption | ].
        eapply CtxLogic.exprTPure. intros.
        reflexivity. } }
  Qed.

  Theorem instantiate_mentionsU
  : @instantiate_mentionsU_spec (expr typ func) (@instantiate typ func) _mentionsU.
  Proof.
    clear.
    red. intros f n e u. revert n.
    induction e; simpl; intros.
    { split; intros. congruence.
      destruct H. destruct H; auto.
      forward_reason; auto. }
    { split; intros. congruence.
      destruct H. destruct H; auto.
      forward_reason; auto. }
    { specialize (IHe1 n). specialize (IHe2 n).
      simpl in *.
      repeat rewrite <- _mentionsU_mentionsU in *.
      transitivity (_mentionsU u (instantiate f n e1) = true \/ _mentionsU u (instantiate f n e2) = true).
      { destruct (_mentionsU u (instantiate f n e1)); intuition. }
      { rewrite IHe1. rewrite IHe2.
        split.
        { destruct 1.
          { destruct H; forward_reason.
            { rewrite H0. left; auto. }
            { right. do 2 eexists; split; [ eassumption | ].
              rewrite H0. eauto. } }
          { destruct H; forward_reason.
            { rewrite H. rewrite H0.
              left. split; auto. destruct (_mentionsU u e1); reflexivity. }
            { right. do 2 eexists; split; eauto.
              split; auto.
              repeat rewrite <- _mentionsU_mentionsU in *.
              destruct (_mentionsU x e1); eauto. } } }
        { destruct 1; forward_reason.
          { rewrite H. destruct (_mentionsU u e1).
            { left. left; auto. }
            { right; left; auto. } }
          { repeat rewrite <- _mentionsU_mentionsU in *.
            consider (_mentionsU x e1).
            { left; right. do 2 eexists; split; eauto. }
            { intros. right; right; do 2 eexists; split; eauto. } } } } }
    { specialize (IHe (S n)). simpl in IHe.
      assert (Morphisms.respectful eq eq (fun _ : ExprI.var => false)
                                   (fun v : var => match v with
                                                     | 0 => false
                                                     | S _ => false
                                                   end)).
      { red. intros; subst; destruct y; auto. }
      (* rewrite Proper_mentionsAny in IHe; [ | reflexivity | eassumption | reflexivity ]. *)
      rewrite IHe. clear - H.
      split; destruct 1; intros;
        try (rewrite Proper_mentionsAny; [ | reflexivity | symmetry; eassumption | reflexivity ]).
      { left; auto. }
      { right. do 2 destruct H0.
        exists x; exists x0. auto. }
      { left; eauto. }
      { right; do 2 destruct H0; exists x; exists x0. auto. } }
    { split.
      { consider (EqNat.beq_nat u u0).
        { intros; subst.
          consider (f u0).
          + intros. right.
            rewrite mentionsU_lift in H0.
            do 2 eexists; split; eauto.
            rewrite <- EqNat.beq_nat_refl. auto.
          + intros. left; auto. }
        { intros. right.
          consider (f u0); intros.
          { do 2 eexists.
            split; eauto.
            rewrite mentionsU_lift in H1.
            rewrite <- EqNat.beq_nat_refl. auto. }
          { simpl in H1.
            exfalso.
            eapply EqNat.beq_nat_true_iff in H1. auto. } } }
      { intros. destruct H.
        { destruct H.
          eapply EqNat.beq_nat_true_iff in H0.
          subst. rewrite H.
          simpl. rewrite <- EqNat.beq_nat_refl. auto. }
        { forward_reason.
          eapply EqNat.beq_nat_true_iff in H0.
          subst.
          rewrite H.
          rewrite mentionsU_lift. assumption. } } }
  Qed.

End instantiate_thm.
