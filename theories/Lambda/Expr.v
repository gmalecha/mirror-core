Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Bool.Bool.
Require Import Coq.omega.Omega.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Export MirrorCore.Lambda.ExprCore.
Require Export MirrorCore.Lambda.ExprD.
Require Export MirrorCore.Lambda.ExprLift.
Require Export MirrorCore.Lambda.ExprSubst.
Require Import MirrorCore.Util.Compat.

Section expr.
  Variable typ : Type.
  Variable func : Type.
  Variable RType_typ : RType typ.
  Variable Typ2_Fun : Typ2 _ RFun.
  Context {RSym_func : RSym func}.

  (** Reasoning principles **)
  Context {RTypeOk_typD : RTypeOk}.
  Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.
  Context {RSymOk_func : RSymOk RSym_func}.

  Lemma Proper_mentionsAny
  : Proper ((@eq uvar ==> @eq bool) ==>
            (@eq var ==> @eq bool) ==>
            @eq (expr typ func) ==> @eq bool) mentionsAny.
  Proof.
    repeat red. intros; subst.
    revert x0 y0 x y H0 H.
    induction y1; simpl; intros; auto.
    { erewrite IHy1_1; eauto. erewrite IHy1_2; eauto. }
    { eapply IHy1; eauto.
      red. intros; subst. destruct y2; eauto. }
  Qed.

  Lemma mentionsU_ind u
  : forall (P : expr typ func -> bool -> Prop),
      (forall v, P (Var v) false) ->
      (forall s, P (Inj s) false) ->
      (forall u', P (UVar u') (u ?[ eq ] u')) ->
      (forall f x rf rx (IHf : P f rf) (IHx : P x rx), P (App f x) (rf || rx)) ->
      (forall t x rx (IHx : P x rx), P (Abs t x) rx) ->
      forall e, P e (_mentionsU u e).
  Proof.
    assert (forall x, (fun _ : ExprI.var => false) x = false) by reflexivity.
    generalize dependent (fun _ : ExprI.var => false).
    induction e; simpl; intros; eauto.
  Qed.

  Theorem typeof_expr_strengthenU_single
  : forall (tus : list typ) (tvs : tenv typ) (e : expr typ func)
           (t t' : typ),
      _mentionsU (length tus) e = false ->
      typeof_expr (tus ++ t :: nil) tvs e = Some t' ->
      typeof_expr tus tvs e = Some t'.
  Proof.
    intros tus tvs e t t' H.
    revert H tvs t'.
    eapply (mentionsU_ind (length tus)); simpl; intros; auto.
    { unfold rel_dec in H; simpl in H.
      consider (EqNat.beq_nat (length tus) u'); intros; try congruence.
      generalize (ListNth.nth_error_length_lt _ _ H0).
      rewrite app_length. simpl. intros.
      rewrite ListNth.nth_error_app_L in H0; auto.
      omega. }
    { forward.
      eapply orb_false_iff in H.
      destruct H.
      erewrite IHf; eauto.
      erewrite IHx; eauto. }
    { forward.
      erewrite IHx; eauto. }
  Qed.

  Theorem exprD'_strengthenU_single
  : forall (tus : list typ) (tvs : tenv typ) (e : expr typ func)
           (t t' : typ)
           (val : exprT (tus ++ t :: nil) tvs (typD t')),
      _mentionsU (length tus) e = false ->
      ExprDsimul.ExprDenote.exprD' (tus ++ t :: nil) tvs t' e = Some val ->
      exists val' : exprT tus tvs (typD t'),
        ExprDsimul.ExprDenote.exprD' tus tvs t' e = Some val' /\
        (forall (us : HList.hlist typD tus)
                (vs : HList.hlist typD tvs) (u : typD t),
           val (HList.hlist_app us (HList.Hcons u HList.Hnil)) vs = val' us vs).
  Proof.
    intros tus tvs e. simpl. revert tvs.
    induction e; simpl; intros; autorewrite with exprD_rw in *; simpl in *.
    { forward. eexists; split; eauto.
      simpl. intros. inv_all; subst. reflexivity. }
    { forward. eexists; split; eauto.
      simpl. intros. inv_all; subst. reflexivity. }
    { forward. inv_all; subst.
      specialize (H4 _ _ _ _ eq_refl H1).
      specialize (IHe2 _ _ _ _ H5 H2).
      forward_reason.
      erewrite typeof_expr_strengthenU_single; eauto.
      rewrite H3; clear H3.
      rewrite H4; clear H4.
      eexists; split; eauto.
      intros.
      unfold AbsAppI.exprT_App.
      autorewrite_with_eq_rw.
      rewrite H6; rewrite H7; reflexivity. }
    { destruct (typ2_match_case t').
      { forward_reason.
        rewrite H1 in *; clear H1.
        unfold Relim in *.
        progress autorewrite_with_eq_rw_in H0.
        progress autorewrite_with_eq_rw.
        forward.
        eapply IHe in H4; eauto.
        forward_reason.
        rewrite H4.
        eexists; split; eauto.
        intros.
        inv_all; subst.
        autorewrite with eq_rw.
        eapply match_eq_match_eq.
        eapply match_eq_match_eq with (F := fun x => x).
        eapply functional_extensionality.
        eauto. }
      { rewrite H1 in *. congruence. } }
    { forward. inv_all; subst.
      cut (u < length tus); intros.
      { eapply nth_error_get_hlist_nth_appL in H0.
        forward_reason.
        rewrite H0 in H1.
        inv_all; subst. simpl in *.
        rewrite H3. rewrite H2.
        eexists; split; eauto.
        simpl. intros. rewrite H4. reflexivity. }
      { eapply nth_error_get_hlist_nth_Some in H1.
        destruct H1. clear H0.
        eapply ListNth.nth_error_length_lt in x0.
        consider (EqNat.beq_nat (length tus) u); try congruence.
        intros. rewrite app_length in *. simpl in *. omega. } }
  Qed.

  Theorem typeof_expr_strengthenV_single
  : forall (tus : list typ) (tvs : tenv typ) (e : expr typ func)
           (t t' : typ),
      _mentionsV (length tvs) e = false ->
      typeof_expr tus (tvs ++ t :: nil) e = Some t' ->
      typeof_expr tus tvs e = Some t'.
  Proof.
    intros tus tvs e t t'.
    revert tvs t'.
    induction e; simpl; intros; auto.
    { eapply RelDec.neg_rel_dec_correct in H.
      generalize (ListNth.nth_error_length_lt _ _ H0).
      rewrite app_length. simpl. intros.
      rewrite ListNth.nth_error_app_L in H0; auto.
      clear - H H1. generalize dependent (length tvs). clear. unfold var in *.
      intros. omega. }
    { forward.
      erewrite IHe1; eauto.
      erewrite IHe2; eauto. }
    { forward.
      erewrite IHe; eauto. }
  Qed.

  Theorem exprD'_strengthenV_single
  : forall (tus : list typ) (tvs : tenv typ) (e : expr typ func)
           (t t' : typ)
           (val : HList.hlist typD tus ->
                  HList.hlist typD (tvs ++ t :: nil) -> typD t'),
      _mentionsV (length tvs) e = false ->
      ExprDsimul.ExprDenote.exprD' tus (tvs ++ t :: nil) t' e = Some val ->
      exists
        val' : HList.hlist typD tus ->
               HList.hlist typD tvs -> typD t',
        ExprDsimul.ExprDenote.exprD' tus tvs t' e = Some val' /\
        (forall (us : HList.hlist typD tus)
                (vs : HList.hlist typD tvs) (u : typD t),
           val us (HList.hlist_app vs (HList.Hcons u HList.Hnil)) = val' us vs).
  Proof.
    intros tus tvs e. simpl. revert tvs.
    induction e; simpl; intros; autorewrite with exprD_rw in *; simpl in *.
    { forward. inv_all; subst.
      cut (v < length tvs); intros.
      { eapply nth_error_get_hlist_nth_appL in H0.
        forward_reason.
        rewrite H0 in H1.
        inv_all; subst. simpl in *.
        rewrite H3. rewrite H2.
        eexists; split; eauto.
        simpl. intros. rewrite H4. reflexivity. }
      { eapply nth_error_get_hlist_nth_Some in H1.
        destruct H1. clear H0.
        eapply ListNth.nth_error_length_lt in x0.
        eapply RelDec.neg_rel_dec_correct in H.
        intros. rewrite app_length in *. simpl in *.
        unfold var in *. omega. } }
    { forward. eexists; split; eauto.
      simpl. intros. inv_all; subst. reflexivity. }
    { forward. inv_all; subst.
      specialize (IHe1 _ _ _ _ H H1).
      specialize (IHe2 _ _ _ _ H4 H2).
      forward_reason.
      erewrite typeof_expr_strengthenV_single; eauto.
      rewrite H3; clear H3.
      rewrite H5; clear H5.
      eexists; split; eauto.
      intros.
      unfold AbsAppI.exprT_App.
      autorewrite_with_eq_rw.
      rewrite H6; rewrite H7; reflexivity. }
    { destruct (typ2_match_case t').
      { forward_reason.
        rewrite H1 in *; clear H1.
        unfold Relim in *.
        progress autorewrite_with_eq_rw_in H0.
        progress autorewrite_with_eq_rw.
        forward.
        eapply (IHe (t :: tvs)) in H4; eauto.
        forward_reason.
        rewrite H4.
        eexists; split; eauto.
        intros.
        inv_all; subst.
        autorewrite with eq_rw.
        eapply match_eq_match_eq.
        eapply match_eq_match_eq with (F := fun x => x).
        eapply functional_extensionality.
        intros.
        eapply (H6 us (HList.Hcons (Rcast_val r x3) vs)). }
      { rewrite H1 in *. congruence. } }
    { forward. eexists; split; eauto.
      simpl. intros. inv_all; subst. reflexivity. }
  Qed.

  Instance Expr_expr : Expr _ (expr typ func) :=
  { exprD' := fun tus tvs e t => ExprDsimul.ExprDenote.exprD' tus tvs t e
  ; wf_Expr_acc := @wf_expr_acc typ func
  ; expr_subst := @_subst _ _
  ; mentionsAny := ExprCore.mentionsAny
  ; mentionsU := _mentionsU
  ; mentionsV := _mentionsV
  }.

  Instance ExprOk_expr : ExprOk Expr_expr :=
  { exprD'_weaken := _
  }.
  { intros. eapply (@ExprFacts.exprD'_weaken _ _ _ _ _ _ _ _ _ _ _).
    eapply H. }
  { eapply exprD'_strengthenU_single. }
  { eapply exprD'_strengthenV_single. }
  { eapply ExprCore.Proper_mentionsAny. }
  { intros. eapply mentionsAny_weaken; eauto. }
  { intros. eapply mentionsAny_factor. }
  { intros. eapply mentionsAny_complete. }
  { eapply _mentionsU_mentionsU. }
  { intros. eapply _mentionsV_mentionsV. }
  { intros. eapply expr_subst_sound; eauto. exact H. }
  { intros; eapply _subst_noop; eauto. }
  { eapply mentionsU_subst. }
  { eapply mentionsV_subst. }
  { eapply Proper_subst. }
  Qed.
End expr.