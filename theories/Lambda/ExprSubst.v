(** This file contains generic functions for manipulating,
 ** (i.e. substituting and finding) unification variables
 **)
Require Import Coq.Classes.Morphisms.
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
Require Import MirrorCore.Util.Nat.

Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.Lambda.ExprTac.

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

  Lemma if_same : forall T (a : bool) (b : T),
      (if a then b else b) = b.
  Proof. clear. destruct a; reflexivity. Qed.

  Lemma mentionsV_lift
  : forall v e a b,
      _mentionsV v (lift (typ := typ) (func := func) a b e) =
      if v ?[ lt ] a then _mentionsV v e
      else if v ?[ lt ] (a + b) then false
           else _mentionsV (v - b) e.
  Proof.
    intros v e; revert v; induction e; intro v_search; simpl; intros; intuition;
    Cases.rewrite_all_goal; repeat rewrite if_same; intuition.
    { repeat match goal with
               | |- context [ match ?X with _ => _ end ] => consider X
             end; intros; auto;
      match goal with
        | |- ?X = ?Y =>
          consider X; consider Y; intros; try reflexivity;
          subst; try solve [ exfalso ; omega ]
      end.
      { rewrite NPeano.Nat.add_sub in H2. congruence. }
      { assert (v_search - b + b = v_search) by omega.
        congruence. } }
    { clear.
      consider (v_search ?[ lt ] a); try reflexivity.
      consider (v_search ?[ lt ] (a + b)); reflexivity. }
    { replace (S v_search ?[ lt ] S a)
         with (v_search ?[ lt ] a).
      { consider (v_search ?[ lt ] a); try reflexivity.
        replace (S v_search ?[ lt ] (S a + b))
           with (v_search ?[ lt ] (a + b)).
        { consider (v_search ?[ lt ] (a + b)); try reflexivity.
          intros. f_equal. omega. }
        { reflexivity. } }
      { reflexivity. } }
  Qed.

End mentionsU.

Section expr_subst.
  Variable typ : Type.
  Variable func : Type.
  Variable lookupU : uvar -> option (expr typ func).
  Variable lookupV : var -> option (expr typ func).

  Fixpoint _subst (under : nat) (e : expr typ func) : expr typ func :=
    match e with
      | Var v =>
        match lt_rem v under with
          | None => e
          | Some v' => match lookupV v' with
                         | None => e
                         | Some e' => lift 0 under e'
                       end
        end
      | Inj _ => e
      | App l r => App (_subst under l) (_subst under r)
      | Abs t e => Abs t (_subst (S under) e)
      | UVar u =>
        match lookupU u with
          | None => UVar u
          | Some e => lift 0 under e
        end
    end.

End expr_subst.

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

  Theorem expr_subst_sound
  : expr_subst_spec_ho
      (fun us vs e t => ExprDsimul.ExprDenote.exprD' us vs t e)
      _mentionsU _mentionsV (@_subst typ func).
  Proof.
    (** exprD'_ind does not seem powerful enough for this **)
    red. intros. subst n. generalize dependent _tvs. revert e'. revert t.
    induction e; simpl; intros.
    { clear H_substU.
      generalize (lt_rem_sound (length _tvs) v).
      consider (lt_rem v (length _tvs)); intros.
      { specialize (H_substV n).
        destruct (substV n).
        { autorewrite with exprD_rw in H1. simpl in *.
          forward. inv_all; subst.
          eapply nth_error_get_hlist_nth_appR in H3; simpl in H3.
          { forward_reason. subst.
            eapply H_substV in H0. forward_reason.
            generalize (exprD'_lift tus' e nil _tvs tvs' x); simpl.
            rewrite H0. intros; forward.
            destruct r.
            eexists; split; eauto.
            revert H3. eapply exprTApR; auto.
            eapply exprTPureR; auto.
            clear - H6 H1.
            intros. rewrite H1; clear H1.
            rewrite H; clear H.
            eapply (H6 c Hnil).
            rewrite NPeano.Nat.add_sub_assoc.
            rewrite Minus.minus_plus.
            apply rel_dec_eq_true; eauto with typeclass_instances.
            omega. }
          { tauto. } }
        { forward_reason; subst.
          autorewrite with exprD_rw in *. simpl in *.
          forward; inv_all; subst.
          eapply nth_error_get_hlist_nth_appR in H1; simpl in H1; eauto.
          forward_reason.
          eapply H_substV in H0. forward_reason.
          consider (nth_error_get_hlist_nth typD (_tvs ++ tvs') v); intros.
          { eapply nth_error_get_hlist_nth_appR in H5; eauto.
            forward_reason. rewrite H0 in H5.
            inv_all; subst. destruct s; simpl in *.
            rewrite H3. eexists; split; eauto.
            revert H4. eapply exprTApR; auto.
            eapply exprTPureR; auto.
            clear - H6 H1.
            intros. rewrite H6. rewrite H1.
            f_equal. auto. }
          { exfalso.
            eapply nth_error_get_hlist_nth_None in H5.
            eapply nth_error_get_hlist_nth_Some in H0.
            destruct H0. simpl in *. clear - H5 x2.
            eapply nth_error_length_lt in x2.
            eapply nth_error_length_ge in H5.
            rewrite app_length in H5. omega. }
          rewrite NPeano.Nat.add_sub_assoc.
          rewrite Minus.minus_plus.
          apply rel_dec_eq_true; eauto with typeclass_instances.
          omega. } }
      { clear H_substV H. subst.
        autorewrite with exprD_rw in *; simpl in *.
        forward; inv_all; subst.
        generalize (nth_error_get_hlist_nth_appL typD tvs _ H2).
        generalize (nth_error_get_hlist_nth_appL typD tvs' _ H2).
        intros; forward_reason. destruct x1; destruct x0; simpl in *.
        revert H6. revert H3.
        Cases.rewrite_all_goal. intros; inv_all; subst.
        rewrite H1. eexists; split; eauto.
        eapply exprTPureR; auto.
        clear - H7 H5. intros.
        rewrite H7. rewrite H5. reflexivity. } }
    { clear H_substU H_substV.
      subst. autorewrite with exprD_rw in *; simpl in *.
      forward. eexists; split; eauto.
      inv_all; subst.
      eapply exprTPureR; auto. }
    { Lemma if_true_or : forall a b : bool,
        a = true \/ b = true ->
        (if a then true else b) = true.
      Proof. clear.
             destruct 1; subst; auto. destruct a; reflexivity.
      Qed.
      match type of IHe2 with
      | ?X -> _ =>
        let HQ := fresh in
        assert (HQ : X);
          [ intros; eapply H_substU; eauto using if_true_or
          | specialize (IHe2 HQ) ; clear HQ ]
      end.
      match type of IHe1 with
      | ?X -> _ =>
        let HQ := fresh in
        assert (HQ : X);
          [ intros; eapply H_substU; eauto using if_true_or
          | specialize (IHe1 HQ) ; clear HQ ]
      end.
      subst. autorewrite with exprD_rw in H1; simpl in H1.
      forward; inv_all; subst.
      specialize (IHe2 _ _ _ _ H1 eq_refl); clear H1.
      specialize (IHe1 _ _ _ _ H0 eq_refl); clear H0.
      match type of IHe2 with
      | ?X -> _ =>
        let HQ := fresh in
        assert (HQ : X);
          [ intros; eapply H_substV; eauto using if_true_or
          | specialize (IHe2 HQ) ; clear HQ ]
      end.
      match type of IHe1 with
      | ?X -> _ =>
        let HQ := fresh in
        assert (HQ : X);
          [ intros; eapply H_substV; eauto using if_true_or
          | specialize (IHe1 HQ) ; clear HQ ]
      end.
      forward_reason.
      autorewrite with exprD_rw. simpl.
      erewrite ExprDsimul.ExprDenote.exprD'_typeof_expr by eauto.
      Cases.rewrite_all_goal.
      eexists; split; eauto.
      revert H2. eapply exprTApR; auto.
      revert H3. eapply exprTApR; auto.
      eapply exprTPureR; auto.
      unfold ExprDsimul.ExprDenote.exprT_App.
      clear.
      match goal with
        | |- context [ match ?X with _ => _ end ] =>
          destruct X
      end.
      intros.
      rewrite H. rewrite H0. reflexivity. }
    { match type of IHe with
      | ?X -> _ =>
        let HQ := fresh in
        assert (HQ : X);
          [ intros; eapply H_substU; eauto using if_true_or
          | specialize (IHe HQ) ; clear HQ ]
      end.
      clear H_substU.
      subst. autorewrite with exprD_rw in *; simpl in *.
      arrow_case_any.
      { red in x1. subst. simpl in *.
        autorewrite with eq_rw in *.
        forward. inv_all. destruct r.
        eapply IHe with (_tvs := x :: _tvs) in H2; eauto.
        forward_reason.
        change_rewrite H2.
        eexists; split; eauto.
        revert H4. eapply exprTApR; auto.
        eapply exprTPureR; auto.
        subst. clear - H_substV.
        match goal with
          | |- context [ match ?X with _ => _ end ] =>
            destruct X
        end.
        intros.
        eapply functional_extensionality. intros.
        eapply (H (Hcons (ExprDsimul.ExprDenote.Rcast_val eq_refl x2) _vs)). }
      { congruence. } }
    { clear H_substV.
      specialize (H_substU u).
      destruct (substU u).
      { autorewrite with exprD_rw in *; simpl in *.
        forward. inv_all; subst.
        specialize (H_substU _ _ (eq_sym (EqNat.beq_nat_refl _)) eq_refl).
        forward_reason.
        generalize (exprD'_lift tus' e nil _tvs tvs' x); simpl.
        change_rewrite H. intros; forward.
        destruct r.
        eexists; split; eauto.
        revert H0. eapply exprTApR; auto.
        eapply exprTPureR; auto.
        clear - H4. intros.
        rewrite H. eapply (H4 c Hnil _vs d). }
      { subst. autorewrite with exprD_rw in *; simpl in *.
        forward. inv_all; subst. destruct r.
        destruct (H_substU _ _ (eq_sym (EqNat.beq_nat_refl _)) eq_refl); clear H_substU.
        forward_reason. change_rewrite H.
        rewrite H1. eexists; split; eauto.
        revert H2. eapply exprTApR; auto.
        eapply exprTPureR; auto. } }
  Qed.

  Lemma mentionsU_subst
  : mentionsU_subst_spec (@_subst _ _) _mentionsU (@_mentionsV typ func).
  Proof.
    clear.
    red. intros substU substV n u e; revert n; induction e.
    { simpl. intros.
      generalize (lt_rem_sound n v).
      destruct (lt_rem v n); intros.
      { forward_reason. subst.
        consider (substV (v - n)); intros.
        { split; intros.
          { right. right.
            exists (v - n). exists e.
            rewrite mentionsU_lift in H1.
            split; auto.
            eapply rel_dec_eq_true; eauto with typeclass_instances.
            clear - H.
            eapply Minus.le_plus_minus_r. omega. }
          { destruct H1; forward_reason; try congruence.
            destruct H1; forward_reason; try congruence.
            rewrite mentionsU_lift.
            cut (x = v - n); intros; subst.
            { congruence. }
            { clear - H1.
              match goal with
                | _ : ?X = _ |- _ => consider X; intros
              end.
              omega. } } }
        { simpl. split; intros; try congruence.
          destruct H1; forward_reason; try congruence.
          destruct H1; forward_reason; try congruence.
          cut (x = v - n); intros; subst.
          { congruence. }
          { clear - H1.
            match goal with
              | _ : ?X = _ |- _ => consider X; intros
            end.
            omega. } } }
      { simpl. split; intros; try congruence.
        destruct H0; forward_reason; try congruence.
        destruct H0; forward_reason; try congruence.
        cut (n + x = v); intros; subst.
        { clear H0. exfalso; omega. }
        { clear - H0.
          match goal with
            | _ : ?X = _ |- _ => consider X; intros
          end.
          omega. } } }
    { simpl; intros.
      split; intros; try congruence.
      destruct H; forward_reason; try congruence.
      destruct H; forward_reason; try congruence. }
    { simpl. intros.
      replace (if _mentionsU u (_subst substU substV n e1)
               then true
               else _mentionsU u (_subst substU substV n e2))
         with (orb (_mentionsU u (_subst substU substV n e1))
                   (_mentionsU u (_subst substU substV n e2))).
      { rewrite Bool.orb_true_iff.
        rewrite IHe1; clear IHe1.
        rewrite IHe2; clear IHe2. clear.
        split; intro;
        repeat match goal with
                 | H : _ \/ _ |- _ => destruct H
               end; forward_reason; Cases.rewrite_all_goal; eauto.
        { right. left.
          exists x. rewrite H. eauto. }
        { right; right.
          exists x. rewrite H. eauto. }
        { left. destruct (_mentionsU u e1); auto. }
        { right. left.
          exists x. rewrite H.
          destruct (_mentionsU x e1); eauto. }
        { right. right.
          exists x. rewrite H.
          destruct (_mentionsV (n + x) e1); eauto. }
        { consider (_mentionsU u e1); intros; eauto. }
        { consider (_mentionsU x e1); [ left | right ]; right; left; eauto. }
        { consider (_mentionsV (n + x) e1); [ left | right ]; right; right; eauto. } }
      { destruct (_mentionsU u (_subst substU substV n e1)); auto. } }
    { intros; simpl. rewrite IHe; clear IHe. reflexivity. }
    { simpl. intros.
      split; intros.
      { consider (substU u0); intros.
        { right. left.
          exists u0. eexists.
          rewrite mentionsU_lift in H0.
          split. 2: eauto.
          symmetry. eapply EqNat.beq_nat_refl. }
        { left. simpl in *. split; auto.
          symmetry in H0. eapply EqNat.beq_nat_eq in H0. subst.
          auto. } }
      { destruct H as [ ? | [ ? | ? ] ]; forward_reason.
        { symmetry in H. eapply EqNat.beq_nat_eq in H. subst.
          rewrite H0. simpl. symmetry. eapply EqNat.beq_nat_refl. }
        { symmetry in H. eapply EqNat.beq_nat_eq in H. subst.
          rewrite H0. rewrite mentionsU_lift. auto. }
        { congruence. } } }
  Qed.

  Lemma lt_S_iff : forall a b, a < b <-> S a < S b.
  Proof.
    clear. split; intros; eauto using Lt.lt_n_S, Lt.lt_S_n.
  Qed.

  Lemma ge_S_iff : forall a b, a >= b <-> S a >= S b.
  Proof.
    clear. split; intros; eauto using Le.le_n_S, Le.le_S_n.
  Qed.

  Ltac learn :=
    repeat match goal with
             | _ : ?X = true |- _ =>
               match X with
                 | rel_dec _ _ => consider X; intros; subst
               end
           end.

  Lemma mentionsV_subst
(*
  : forall (substU : uvar -> option (expr typ func)) substV n v e,
      _mentionsV v (_subst substU substV n e) = true <->
      (   (v < n /\ _mentionsV v e = true)
       \/ (v >= n /\
           (   (_mentionsV v e = true /\ substV (v-n) = None)
            \/ (exists u' e', _mentionsU u' e = true /\
                              substU u' = Some e' /\
                              _mentionsV (v-n) e' = true)
            \/ (exists v' e', _mentionsV (v'+n) e = true /\
                              substV v' = Some e' /\
                              _mentionsV (v-n) e' = true)))).
*)
  : mentionsV_subst_spec (@_subst _ _) _mentionsU (@_mentionsV typ func).
  Proof.
    clear. red.
    intros substU substV n v_search e; revert n; revert v_search;
    induction e; intros v_search n; intros.
    { simpl.
      generalize (lt_rem_sound n v).
      destruct (lt_rem v n); intros; forward_reason; subst.
      { consider (substV (v - n)); intros.
        { rewrite mentionsV_lift. simpl.
          split; intros; forward.
          { right. split; [ omega | ].
            right. right. do 2 eexists.
            split; [ | split; eassumption ].
            eapply rel_dec_eq_true. eauto with typeclass_instances.
            clear - H.
            rewrite Plus.plus_comm.
            eapply Minus.le_plus_minus_r. omega. }
          { destruct H1; forward_reason.
            { exfalso. learn. intros; subst. omega. }
            destruct H2 as [ ? | [ ? | ? ] ]; forward_reason.
            { learn. congruence. }
            { congruence. }
            { learn. replace (x + n - n) with x in H0 by omega.
              rewrite H3 in *. inv_all; subst. rewrite H4.
              match goal with
                | |- context [ if ?X then _ else _ ] => consider X; intros
              end; auto.
              exfalso; omega. } } }
        { simpl. split; intros.
          { right.
            learn.
            split; [ omega | ]. left; eauto. }
          { destruct H1; forward_reason; learn; auto.
            destruct H2 as [ ? | [ ? | ? ] ];
              forward_reason; learn; auto; try congruence.
            replace (x + n - n) with x in H0 by omega. congruence. } } }
      { simpl. split; intros; learn.
        { left; auto. }
        { destruct H0; forward_reason; learn; auto.
          destruct H1 as [ ? | [ ? | ? ] ];
            forward_reason; learn; auto; try congruence.
          exfalso; omega. } } }
    { simpl. split; intros; try congruence.
      destruct H; forward_reason; try congruence.
      destruct H0 as [ ? | [ ? | ? ] ]; forward_reason; congruence. }
    { simpl.
      replace (if _mentionsV v_search (_subst substU substV n e1)
               then true
               else _mentionsV v_search (_subst substU substV n e2))
         with (orb (_mentionsV v_search (_subst substU substV n e1))
                   (_mentionsV v_search (_subst substU substV n e2))).
      { rewrite Bool.orb_true_iff.
        rewrite IHe1; clear IHe1.
        rewrite IHe2; clear IHe2.
        split; intros;
        repeat match goal with
                 | H : _ \/ _ |- _ => destruct H; forward_reason
               end; Cases.rewrite_all_goal; eauto.
        { right. split; auto.
          right. left. do 2 eexists; split; [ | split; eassumption ].
          rewrite H0. reflexivity. }
        { right. split; auto.
          right; right. do 2 eexists; split; [ | split; eassumption ].
          rewrite H0. reflexivity. }
        { left. split; auto. destruct (_mentionsV v_search e1); reflexivity. }
        { right. split; auto.
          left. destruct (_mentionsV v_search e1); eauto. }
        { right. split; auto.
          right. left. do 2 eexists; split; [ | split; eassumption ].
          rewrite H0. destruct (_mentionsU x e1); reflexivity. }
        { right. split; auto.
          right. right. do 2 eexists; split; [ | split; eassumption ].
          rewrite H0. destruct (_mentionsV (x+n) e1); reflexivity. }
        { consider (_mentionsV v_search e1); intros.
          { left; left; eauto. }
          { right; left; eauto. } }
        { consider (_mentionsV v_search e1); intros.
          { left. right. split; eauto. }
          { right; right; split; eauto. } }
        { consider (_mentionsU x e1); intros.
          { left; right; split; eauto.
            right; left. do 2 eexists; split; [ | split; eassumption ]; eauto. }
          { right; right; split; eauto.
            right; left. do 2 eexists; split; [ | split; eassumption ]; eauto. } }
        { consider (_mentionsV (x + n) e1);
          intros; [ left | right ]; right; split; eauto;
          (right; right; do 2 eexists; split; [ | split; eassumption ]; eauto). } }
      { destruct (_mentionsV v_search (_subst substU substV n e1)); reflexivity. } }
    { simpl. rewrite IHe; clear IHe.
      rewrite <- lt_S_iff.
      rewrite <- ge_S_iff.
      eapply or_iff_compat_l.
      eapply and_iff_compat_l.
      eapply or_iff_compat_l.
      simpl.
      split; (destruct 1; [ left | right ]); forward_reason;
      (do 2 eexists; split; [ | split; [ eassumption | ] ]; eauto).
      rewrite <- plus_n_Sm in *. eauto.
      rewrite <- plus_n_Sm in *. eauto. }
    { simpl.
      consider (substU u); intros.
      { rewrite mentionsV_lift. simpl in *.
        split; intros; forward.
        { right. split; [ omega | ].
          right. left.
          do 2 eexists; split; [ | split; eassumption ]; eauto.
          symmetry. eapply EqNat.beq_nat_refl. }
        { destruct H0; forward_reason; try congruence.
          destruct H1 as [ ? | [ ? | ? ] ]; forward_reason; try congruence.
          consider (EqNat.beq_nat x u); intros; subst.
          consider (v_search ?[ lt ] n); intros; try omega.
          congruence. } }
      { simpl. split; intros; try congruence.
        destruct H0; forward_reason; try congruence.
        destruct H1 as [ ? | [ ? | ? ] ]; forward_reason; try congruence.
        consider (EqNat.beq_nat x u); intros; subst. congruence. } }
  Qed.

  Theorem Proper_subst
  : Proper ((eq ==> eq) ==> (eq ==> eq) ==> eq ==> eq ==> eq)%signature
           (@_subst typ func).
  Proof.
    clear.
    repeat red. intros. subst.
    revert y1.
    induction y2; intros; simpl; eauto.
    { forward. erewrite H0. reflexivity. reflexivity. }
    { Cases.rewrite_all_goal. reflexivity. }
    { rewrite IHy2. reflexivity. }
    { erewrite H; reflexivity. }
  Qed.

  Theorem _subst_noop
  : forall (substU : ExprI.uvar -> option (expr typ func))
           (substV : ExprI.var -> option (expr typ func))
     (n : nat) (e : expr typ func),
      (forall u : ExprI.uvar, _mentionsU u e = true -> substU u = None) ->
      (forall v : ExprI.var, _mentionsV (v+n) e = true -> substV v = None) ->
      _subst substU substV n e = e.
  Proof.
    intros substU substV n e; revert n; induction e; simpl; eauto.
    { intros.
      generalize (lt_rem_sound n v).
      destruct (lt_rem v n); intros; forward_reason; subst.
      { rewrite H0. reflexivity.
        eapply EqNat.beq_nat_true_iff. omega. }
      { reflexivity. } }
    { simpl; intros.
      rewrite IHe1; clear IHe1.
      rewrite IHe2; clear IHe2.
      reflexivity.
      { intros. eapply H. rewrite H1.
        destruct (_mentionsU u e1); reflexivity. }
      { intros. eapply H0. rewrite H1.
        destruct (_mentionsV (v+n) e1); reflexivity. }
      { intros. eapply H. rewrite H1.
        destruct (_mentionsU u e1); reflexivity. }
      { intros. eapply H0. rewrite H1.
        destruct (_mentionsV (v+n) e1); reflexivity. } }
    { intros. rewrite IHe; eauto. intros.
      eapply H0. rewrite <- H1. f_equal. omega. }
    { intros.
      rewrite H. reflexivity. symmetry.
      eapply EqNat.beq_nat_refl. }
  Qed.
(**
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
  : @mentionsU_instantiate_spec (expr typ func) (@instantiate typ func) _mentionsU.
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
**)
End instantiate_thm.
