Require Import Coq.Bool.Bool.
Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.VariablesI.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprDFacts.
Require MirrorCore.Lambda.ExprDsimul.

Require Import FunctionalExtensionality.

Set Implicit Arguments.
Set Strict Implicit.

Export ExprDsimul.ExprDenote.

Module ExprFacts := ExprDFacts.Make ExprDsimul.ExprDenote.

Section Expr.
  Context {typ : Type}
          {func : Type}.
  Context {RT : RType typ}
          {T2 : Typ2 _ PreFun.Fun}
          {RS : RSym func}.

  Instance Expr_expr : @Expr typ _ (@expr typ func) :=
  { exprD' := fun tus tvs e t => @exprD' _ _ _ _ _ tus tvs t e
  ; wf_Expr_acc := @wf_expr_acc typ func
(*  ; mentionsAny := mentionsAny *)
  }.

  Context {RTOk : RTypeOk}
          {T2Ok : Typ2Ok T2}
          {RSOk : RSymOk RS}.

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
           (val : HList.hlist typD (tus ++ t :: nil) ->
                  HList.hlist typD tvs -> typD t'),
      _mentionsU (length tus) e = false ->
      ExprI.exprD' (tus ++ t :: nil) tvs e t' = Some val ->
      exists
        val' : HList.hlist typD tus ->
               HList.hlist typD tvs -> typD t',
        ExprI.exprD' tus tvs e t' = Some val' /\
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
      unfold exprT_App.
      autorewrite with eq_rw.
      rewrite H6; rewrite H7; reflexivity. }
    { destruct (typ2_match_case t').
      { forward_reason.
        rewrite H1 in *; clear H1.
        unfold Relim in *.
        autorewrite with eq_rw in *.
        forward.
        eapply IHe in H3; eauto.
        forward_reason.
        rewrite H3.
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
      omega. }
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
      ExprI.exprD' tus (tvs ++ t :: nil) e t' = Some val ->
      exists
        val' : HList.hlist typD tus ->
               HList.hlist typD tvs -> typD t',
        ExprI.exprD' tus tvs e t' = Some val' /\
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
        intros. rewrite app_length in *. simpl in *. omega. } }
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
      unfold exprT_App.
      autorewrite with eq_rw.
      rewrite H6; rewrite H7; reflexivity. }
    { destruct (typ2_match_case t').
      { forward_reason.
        rewrite H1 in *; clear H1.
        unfold Relim in *.
        repeat first [ rewrite eq_Const_eq in *
                     | rewrite eq_option_eq in *
                     | rewrite eq_Arr_eq in * ].
        forward.
        eapply (IHe (t :: tvs)) in H3; eauto.
        forward_reason.
        rewrite H3.
        eexists; split; eauto.
        intros.
        inv_all; subst.
        autorewrite with eq_rw.
        eapply match_eq_match_eq.
        eapply match_eq_match_eq with (F := fun x => x).
        eapply functional_extensionality.
        intros.
        eapply (H5 us (HList.Hcons (Rcast_val r x3) vs)). }
      { rewrite H1 in *. congruence. } }
    { forward. eexists; split; eauto.
      simpl. intros. inv_all; subst. reflexivity. }
  Qed.

  Instance ExprOk_expr : ExprOk Expr_expr.
  Proof.
    constructor.
    { simpl. intros.
      eapply ExprFacts.exprD'_weaken; eauto. }
  Qed.
(*
    { eapply exprD'_strengthenU_single. }
    { eapply exprD'_strengthenV_single. }
    { simpl. eapply Proper_mentionsAny. }
    { simpl. intros; eapply mentionsAny_factor. }
  Qed.
*)


End Expr.

Export MirrorCore.Lambda.ExprCore.
Export MirrorCore.SymI.
