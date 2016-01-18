(** This file contains generic functions for manipulating,
 ** (i.e. substituting and finding) unification variables
 **)
Require Import Coq.omega.Omega.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.Util.Nat.
Require Import MirrorCore.Util.Compat.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.Lambda.ExprDFacts.
Require Import MirrorCore.Lambda.ExprD.

Set Implicit Arguments.
Set Strict Implicit.

Require Import Coq.Logic.FunctionalExtensionality.

Section substitute.
  Variable typ : Type.
  Variable func : Type.

  Section subst'.
    Variable lookupU : uvar -> forall t, (expr typ func -> t) -> t -> t.
    Variable lookupV : var -> forall t, (expr typ func -> t) -> t -> t.

    Fixpoint subst' (lift_by : nat) (e : expr typ func)
    : expr typ func :=
      match e with
        | Var v => match lt_rem v lift_by with
                     | None => Var v
                     | Some diff =>
                       lookupV diff (lift 0 lift_by) e
                   end
        | Inj _ => e
        | UVar u => lookupU u (lift 0 lift_by) e
        | App l r => App (subst' lift_by l) (subst' lift_by r)
        | Abs t e => Abs t (subst' (S lift_by) e)
      end.
  End subst'.

  Definition subst
             (lookupU : uvar -> forall t, (expr typ func -> t) -> t -> t)
             (lookupV : var -> forall t, (expr typ func -> t) -> t -> t)
             (under : nat) (e : expr typ func)
  : expr typ func :=
    subst' lookupU lookupV under e.

  Variable RType_typ : RType typ.
  Variable Typ2_Fun : Typ2 _ RFun.
  Context {RSym_func : RSym func}.

  (** Reasoning principles **)
  Context {RTypeOk_typD : RTypeOk}.
  Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.
  Context {RSymOk_func : RSymOk RSym_func}.

(*
  Theorem lift_0 : forall (e : expr typ func) u, Lift.lift u 0 e = e.
  Proof.
    induction e; simpl; intros; Cases.rewrite_all_goal; auto.
    consider (v ?[ lt ] u); auto.
  Qed.
*)

  Definition Natural {T} (f : forall t, (T -> t) -> t -> t) : Prop :=
       (exists v, forall t ret none, f t ret none = ret v)
    \/ (forall t ret none, f t ret none = none).

  Lemma typeof_expr_subst'
  : forall (lookupU lookupV : nat -> forall t, (expr _ _ -> t) -> t -> t) tus tus' tvs tvs'
      (HNU : forall n, Natural (lookupU n))
      (HNV : forall n, Natural (lookupV n))
      (HlookupV : forall v e t,
         nth_error tvs v = Some t ->
         typeof_expr tus tvs e = Some t ->
         typeof_expr tus' tvs' (lookupV v _ (fun x => x) e) = Some t)
      (HlookupU : forall u e t,
         nth_error tus u = Some t ->
         typeof_expr tus tvs e = Some t ->
         typeof_expr tus' tvs' (lookupU u _ (fun x => x) e) = Some t)
      e y tvex,
      typeof_expr tus (tvex ++ tvs) e = Some y ->
      typeof_expr tus' (tvex ++ tvs')
                     (subst' lookupU lookupV (length tvex) e) = Some y.
  Proof.
    induction e; simpl; intros; eauto.
    { generalize (lt_rem_sound (length tvex) v).
      destruct (lt_rem v (length tvex)); intros.
      { destruct H0; subst.
        specialize (HlookupV (v - length tvex)).
        destruct (HNV (v - length tvex)).
        { destruct H1.
          revert HlookupV.
          setoid_rewrite H1.
          intros.
          etransitivity; [ eapply (@typeof_expr_lift _ _ _ _ _ tus' x nil tvex tvs') | ].
          simpl.
          rewrite nth_error_app_R in H; eauto.
          eapply H2; eauto.
          instantiate (1 := Var (v - length tvex)).
          eauto. }
        { generalize (HlookupV (Var (v - length tvex)) y). setoid_rewrite H1.
          simpl. intros.
          rewrite nth_error_app_R in H; eauto.
          rewrite nth_error_app_R; eauto. } }
      { rewrite nth_error_app_L in H; auto.
        simpl. rewrite nth_error_app_L; auto. } }
    { forwardy.
      erewrite IHe1; eauto.
      erewrite IHe2; eauto. }
    { forwardy.
      inv_all; subst.
      specialize (IHe y0 (t :: tvex)); simpl in IHe.
      rewrite IHe; auto. }
    { generalize (HlookupU u).
      destruct (HNU u) as [ [ ? ? ] | ? ]; setoid_rewrite H0.
      { etransitivity.
        eapply (@typeof_expr_lift _ _ _ _ _ tus' _ nil tvex tvs').
        simpl. eapply H1; eauto.
        instantiate (1 := UVar u). assumption. }
      { simpl. intros.
        specialize (H1 (UVar u) y). auto. } }
  Qed.

  Theorem lambda_exprD_subst'
  : forall lookupU lookupV tus tvs tus' tvs' P
      (HNU : forall u, Natural (lookupU u)) (HNV : forall v, Natural (lookupV v))
      (HlookupV : forall t e v vD vD_orig,
         nth_error_get_hlist_nth _ tvs v = Some (@existT _ _ t vD) ->
         lambda_exprD tus tvs t e = Some vD_orig ->
         exists vD',
           lambda_exprD tus' tvs' t (lookupV v _ (fun x => x) e) = Some vD' /\
           forall us vs us' vs',
             P us vs us' vs' ->
             vD_orig us vs = vD vs ->
             vD vs = vD' us' vs')
      (HlookupU : forall t e v vD vD_orig,
         nth_error_get_hlist_nth _ tus v = Some (@existT _ _ t vD) ->
         lambda_exprD tus tvs t e = Some vD_orig ->
         exists vD',
           lambda_exprD tus' tvs' t (lookupU v _ (fun x => x) e) = Some vD' /\
           forall us vs us' vs',
             P us vs us' vs' ->
             vD_orig us vs = vD us ->
             vD us = vD' us' vs'),
      forall e tvex (t : typ) eD,
        lambda_exprD tus (tvex ++ tvs) t e = Some eD ->
        exists eD',
          lambda_exprD tus' (tvex ++ tvs') t (subst' lookupU lookupV (length tvex) e) = Some eD' /\
          forall us vs us' vs' vex,
            P us vs us' vs' ->
            eD us (hlist_app vex vs) = eD' us' (hlist_app vex vs').
  Proof.
    induction e; simpl; intros.
    { generalize (lt_rem_sound (length tvex) v).
      destruct (lt_rem v (length tvex)).
      { destruct 1.
        destruct (HNV n) as [ [ ? ? ] | ? ].
        { generalize (HlookupV t (Var n) n); clear HlookupU HlookupV.
          autorewrite with exprD_rw in *; simpl in *.
          subst.
          forwardy.
          eapply nth_error_get_hlist_nth_appR in H0; eauto.
          simpl in *. forward_reason; inv_all; subst.
          Cases.rewrite_all_goal.
          destruct y.
          intro XXX; specialize (XXX _ _ eq_refl eq_refl).
          forward_reason.
          generalize (lambda_exprD_lift tus' x nil tvex tvs' x0).
          simpl. rewrite H3. intros; forwardy.
          eexists; split; [ eassumption | ].
          intros.
          etransitivity; [ | eapply (H7 us' Hnil vex vs') ].
          rewrite H4.
          eapply H5; eauto. }
        { generalize (HlookupV t (Var n) n); clear HlookupU HlookupV.
          autorewrite with exprD_rw in *; simpl in *.
          subst.
          forwardy.
          generalize H0.
          eapply nth_error_get_hlist_nth_appR in H0; eauto.
          simpl in *. forward_reason; inv_all; subst.
          Cases.rewrite_all_goal.
          destruct y.
          intro.
          intro XXX; specialize (XXX _ _ eq_refl eq_refl).
          forward_reason.
          generalize (lambda_exprD_lift tus' (Var (v - length tvex)) nil tvex tvs' x).
          simpl. rewrite H5. intros; forwardy.
          cutrewrite (v - length tvex + length tvex = v) in H7; [ | omega ].
          eexists; split; [ eassumption | ].
          intros.
          etransitivity; [ | eapply (H8 us' Hnil vex vs') ].
          rewrite H4.
          eapply H6; eauto. } }
      { intros.
        autorewrite with exprD_rw in *; simpl in *.
        forwardy.
        generalize (@nth_error_get_hlist_nth_appL _ typD tvs' _ _ H0).
        generalize (@nth_error_get_hlist_nth_appL _ typD tvs _ _ H0).
        clear H0.
        intros; forward_reason; inv_all; subst.
        revert H4 H0. Cases.rewrite_all_goal.
        destruct x0; destruct x1; simpl in *.
        intros; inv_all; subst.
        Cases.rewrite_all_goal.
        eexists; split; [ reflexivity | ].
        simpl. intros.
        Cases.rewrite_all_goal. reflexivity. } }
    { autorewrite with exprD_rw in *; simpl in *.
      forwardy.
      rewrite H. eexists; split; [ reflexivity | ].
      inv_all; subst.
      reflexivity. }
    { autorewrite with exprD_rw in *; simpl in *.
      forwardy.
      inv_all; subst.
      eapply IHe1 in H0; clear IHe1.
      eapply IHe2 in H1; clear IHe2.
      forward_reason.
      rewrite typeof_expr_subst' with (tvs := tvs) (tus := tus) (y := y); eauto.
      { rewrite H1; clear H1.
        rewrite H0; clear H0.
        eexists; split; [ reflexivity | ].
        unfold AbsAppI.exprT_App; intros; autorewrite_with_eq_rw.
        erewrite H2; eauto. erewrite H3; eauto. }
      { intros.
        assert (exists vD,
                  lambda_exprD tus tvs t0 e = Some vD)
          by (eapply ExprFacts.typeof_expr_lambda_exprD; eauto).
        destruct H6.
        consider (nth_error_get_hlist_nth typD tvs v); intros.
        { destruct s.
          assert (x2 = t0).
          { eapply nth_error_get_hlist_nth_Some in H7. destruct H7.
            clear - H4 x3. simpl in *. congruence. }
          subst.
          eapply HlookupV with (v := v) in H6; eauto.
          forward_reason. eapply ExprFacts.lambda_exprD_typeof_expr.
          eauto. }
        { clear - H4 H7; exfalso.
          eapply nth_error_get_hlist_nth_None in H7. congruence. } }
      { intros.
        assert (exists vD,
                  lambda_exprD tus tvs t0 e = Some vD)
          by (eapply ExprFacts.lambda_exprD_typeof_expr; eauto).
        destruct H6.
        consider (nth_error_get_hlist_nth typD tus u); intros.
        { destruct s.
          assert (x2 = t0).
          { eapply nth_error_get_hlist_nth_Some in H7. destruct H7.
            clear - H4 x3. simpl in *. congruence. }
          subst.
          eapply HlookupU with (v := u) in H6; eauto.
          forward_reason. eapply ExprFacts.lambda_exprD_typeof_expr.
          eauto. }
        { clear - H4 H7; exfalso.
          eapply nth_error_get_hlist_nth_None in H7. congruence. } } }
    { autorewrite with exprD_rw in *; simpl in *.
      match goal with
        | H : appcontext [ @typ2_match _ _ _ _ _ ?Y ] |- _ =>
          let H := fresh in
          destruct (@typ2_match_case _ _ _ _ _ Y) as [ [ ? [ ? [ ? H ] ] ] | H ];
            ( try rewrite H in * )
      end; clear H0.
      { unfold Relim in *. red in x1; subst.
        destruct (eq_sym (typ2_cast x x0)).
        forward.
        eapply IHe with (tvex := t :: tvex) in H0.
        forward_reason. simpl in *.
        rewrite H0.
        eexists; split; [ reflexivity | ].
        inv_all; subst.
        intros. eapply functional_extensionality.
        intros.
        eapply (H2 us vs us' vs' (Hcons (Rcast_val r x2) vex)); assumption. }
      { congruence. } }
    { generalize (HlookupU t (UVar u) u); clear HlookupU HlookupV.
      autorewrite with exprD_rw in *; simpl in *.
      forwardy.
      inv_all; subst.
      rewrite H. rewrite H0.
      intro HlookupU.
      destruct y.
      specialize (HlookupU _ _ eq_refl eq_refl).
      forward_reason.
      destruct (HNU u).
      { forward_reason.
        rewrite H3 in H1.
        specialize (H3 _ (lift 0 (length tvex)) (UVar u)).
        rewrite H3.
        generalize (lambda_exprD_lift tus' x1 nil tvex tvs' x); simpl.
        rewrite H1. intros.
        forwardy.
        eexists; split; [ eassumption | ].
        intros. etransitivity; [ eapply H2 | ]; eauto.
        eapply (H5 us' Hnil vex vs'). }
      { rewrite H3 in *.
        revert H1. autorewrite with exprD_rw; simpl.
        intros. forward.
        eexists; split; [ reflexivity | ].
        inv_all; subst; intros.
        eapply H2; eauto. } }
  Qed.

  Theorem lambda_exprD_subst
  : forall tus tvs tus' tvs' lookupU lookupV P (e : expr typ func) (t : typ),
      (forall u, Natural (lookupU u)) -> (forall v, Natural (lookupV v)) ->
      (forall t e v vD vD_orig,
         nth_error_get_hlist_nth _ tvs v = Some (@existT _ _ t vD) ->
         lambda_exprD tus tvs t e = Some vD_orig ->
         exists vD',
           lambda_exprD tus' tvs' t (lookupV v _ (fun x => x) e) = Some vD' /\
           forall us vs us' vs',
             P us vs us' vs' ->
             vD_orig us vs = vD vs ->
             vD vs = vD' us' vs') ->
      (forall t e v vD vD_orig,
         nth_error_get_hlist_nth _ tus v = Some (@existT _ _ t vD) ->
         lambda_exprD tus tvs t e = Some vD_orig ->
         exists vD',
           lambda_exprD tus' tvs' t (lookupU v _ (fun x => x) e) = Some vD' /\
           forall us vs us' vs',
             P us vs us' vs' ->
             vD_orig us vs = vD us ->
             vD us = vD' us' vs') ->
      forall tvx eD,
        lambda_exprD tus (tvx ++ tvs) t e = Some eD ->
      exists eD',
        lambda_exprD tus' (tvx ++ tvs') t (subst lookupU lookupV (length tvx) e) = Some eD' /\
        forall us vs us' vs' vx,
          P us vs us' vs' ->
          eD us (hlist_app vx vs) = eD' us' (hlist_app vx vs').
  Proof.
    intros.
    eapply (@lambda_exprD_subst' lookupU lookupV tus tvs tus' tvs' P)
      with (tvex := tvx) in H1; eauto.
  Qed.

  Definition mentions (uv : nat + nat) (e : expr typ func) : bool :=
    match uv with
      | inl u => _mentionsU u e
      | inr v => _mentionsV v e
    end.

  Lemma mentions_App
  : forall uv e1 e2,
      mentions uv (App e1 e2) =
      orb (mentions uv e1) (mentions uv e2).
  Proof. destruct uv; reflexivity. Qed.

  Definition lift_uv (uv : nat + nat) (n : nat) : nat + nat :=
    match uv with
      | inl u => inl u
      | inr v => inr (v + n)
    end.

  Lemma mentions_Abs
  : forall e uv t,
      mentions uv (Abs t e) = match uv with
                                | inl u => mentions (inl u) e
                                | inr v => mentions (inr (S v)) e
                              end.
  Proof.
    destruct uv; simpl; auto.
  Qed.

  Lemma mentions_Inj : forall x f, mentions x (Inj f) = false.
    destruct x; reflexivity.
  Qed.

  Lemma mentionsV_lift
  : forall n n0 (x : expr typ func) z,
      _mentionsV (z + n0 + n) (lift z n x) = _mentionsV (z + n0) x.
  Proof.
    induction x; simpl; intros; auto.
    { consider (v ?[ lt ] z).
      { intros.
        match goal with
          | |- ?X = ?Y =>
            consider X; consider Y; auto; try solve [ intros; exfalso ; omega ]
        end. }
      { intros.
        match goal with
          | |- ?X = ?Y =>
            consider X; consider Y; auto; try solve [ intros; exfalso ; omega ]
        end. intros.
        rewrite NPeano.Nat.add_cancel_r in H1. exfalso; auto. } }
    { rewrite IHx1. rewrite IHx2. reflexivity. }
    { specialize (IHx (S z)). apply IHx. }
  Qed.

  Lemma or_rearrange : forall (A B C D : Prop),
                         (A \/ B) \/ C \/ D <->
                         (A \/ C) \/ (B \/ D).
  Proof. clear; intuition. Qed.
  Lemma or_iff : forall A B C D : Prop,
                   (A <-> B) -> (C <-> D) ->
                   ((A \/ C) <-> (B \/ D)).
  Proof. clear. intuition. Qed.
  Lemma exists_or : forall (T : Type) (P Q : T -> Prop),
                      ((exists x : T, P x) \/ (exists x : T, Q x)) <->
                      (exists x, P x \/ Q x).
  Proof. clear. intuition; forward_reason; eauto.
         destruct H. left; eauto. right; eauto.
  Qed.
  Lemma exists_iff : forall (T : Type) (P Q : T -> Prop),
                       (forall x, P x <-> Q x) ->
                       ((exists x, P x) <-> (exists y, Q y)).
  Proof. clear. intuition; forward_reason; intuition eauto.
         eapply H in H0; eauto. eapply H in H0; eauto.
  Qed.
  Lemma or_factor : forall A B C : Prop,
                      ((A /\ B) \/ (A /\ C)) <-> A /\ (B \/ C).
  Proof. clear. intuition. Qed.

  Lemma false_eq_true_False : false = true <-> False.
  Proof. intuition. Qed.
  Lemma False_and : forall A, (False /\ A) <-> False.
  Proof. intuition. Qed.
  Lemma False_or : forall A, (False \/ A) <-> A.
  Proof. intuition. Qed.

End substitute.