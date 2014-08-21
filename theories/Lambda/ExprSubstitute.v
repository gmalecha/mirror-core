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
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprDI.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.Lambda.ExprDFacts.
Require Import MirrorCore.Lambda.ExprD.

Set Implicit Arguments.
Set Strict Implicit.

Require Import FunctionalExtensionality.

Section substitute.
  Variable typ : Type.
  Variable func : Type.

  Fixpoint lt_rem (a b : nat) : option nat :=
    match b with
      | 0 => Some a
      | S b' => match a with
                  | 0 => None
                  | S a' => lt_rem a' b'
                end
    end.

  Lemma lt_rem_sound
  : forall b a,
      match lt_rem a b with
        | None => a < b
        | Some c => a >= b /\ a - b = c
      end.
  Proof.
    induction b; destruct a; simpl; intros; auto.
    { split; auto. red. omega. }
    { omega. }
    { specialize (IHb a).
      destruct (lt_rem a b); intuition. }
  Qed.

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
  Variable Typ2_Fun : Typ2 _ Fun.
  Context {RSym_func : RSym func}.

  (** Reasoning principles **)
  Context {RTypeOk_typD : RTypeOk}.
  Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.
  Context {RSymOk_func : RSymOk RSym_func}.

  Variable ts : list Type.

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
         typeof_expr ts tus tvs e = Some t ->
         typeof_expr ts tus' tvs' (lookupV v _ (fun x => x) e) = Some t)
      (HlookupU : forall u e t,
         nth_error tus u = Some t ->
         typeof_expr ts tus tvs e = Some t ->
         typeof_expr ts tus' tvs' (lookupU u _ (fun x => x) e) = Some t)
      e y tvex,
      typeof_expr ts tus (tvex ++ tvs) e = Some y ->
      typeof_expr ts tus' (tvex ++ tvs')
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
          etransitivity; [ eapply (@typeof_expr_lift _ _ _ _ _ ts tus' x nil tvex tvs') | ].
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
        eapply (@typeof_expr_lift _ _ _ _ _ ts tus' _ nil tvex tvs').
        simpl. eapply H1; eauto.
        instantiate (1 := UVar u). assumption. }
      { simpl. intros.
        specialize (H1 (UVar u) y). auto. } }
  Qed.

  Theorem exprD'_subst'
  : forall lookupU lookupV tus tvs tus' tvs' P
      (HNU : forall u, Natural (lookupU u)) (HNV : forall v, Natural (lookupV v))
      (HlookupV : forall t e v vD vD_orig,
         nth_error_get_hlist_nth _ tvs v = Some (@existT _ _ t vD) ->
         exprD' ts tus tvs t e = Some vD_orig ->
         exists vD',
           exprD' ts tus' tvs' t (lookupV v _ (fun x => x) e) = Some vD' /\
           forall us vs us' vs',
             P us vs us' vs' ->
             vD_orig us vs = vD vs ->
             vD vs = vD' us' vs')
      (HlookupU : forall t e v vD vD_orig,
         nth_error_get_hlist_nth _ tus v = Some (@existT _ _ t vD) ->
         exprD' ts tus tvs t e = Some vD_orig ->
         exists vD',
           exprD' ts tus' tvs' t (lookupU v _ (fun x => x) e) = Some vD' /\
           forall us vs us' vs',
             P us vs us' vs' ->
             vD_orig us vs = vD us ->
             vD us = vD' us' vs'),
      forall e tvex (t : typ) eD,
        exprD' ts tus (tvex ++ tvs) t e = Some eD ->
        exists eD',
          exprD' ts tus' (tvex ++ tvs') t (subst' lookupU lookupV (length tvex) e) = Some eD' /\
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
          generalize (exprD'_lift ts tus' x nil tvex tvs' x0).
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
          generalize (exprD'_lift ts tus' (Var (v - length tvex)) nil tvex tvs' x).
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
        generalize H0.
        eapply nth_error_get_hlist_nth_appL with (tvs' := tvs') in H0.
        intro H3.
        eapply nth_error_get_hlist_nth_appL with (tvs' := tvs) in H3.
        forward_reason.
        rewrite H0. destruct x0; simpl in *.
        red in y. subst.
        rewrite H3 in H.
        rewrite H6 in H4.
        inv_all; subst.
        destruct x1; simpl in *.
        rewrite H1. eexists; split; [ reflexivity | ].
        intros. simpl. rewrite H7. rewrite H5. reflexivity. } }
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
        unfold Open_App, OpenT, ResType.OpenT; intros; autorewrite with eq_rw.
        erewrite H2; eauto. erewrite H3; eauto. }
      { intros.
        assert (exists vD,
                  exprD' ts tus tvs t0 e = Some vD)
          by (eapply ExprFacts.typeof_expr_exprD'; eauto).
        destruct H6.
        consider (nth_error_get_hlist_nth (typD ts) tvs v); intros.
        { destruct s.
          assert (x2 = t0).
          { eapply nth_error_get_hlist_nth_Some in H7. destruct H7.
            clear - H4 x3. simpl in *. congruence. }
          subst.
          eapply HlookupV with (v := v) in H6; eauto.
          forward_reason. eapply ExprFacts.exprD'_typeof_expr.
          eauto. }
        { clear - H4 H7; exfalso.
          eapply nth_error_get_hlist_nth_None in H7. congruence. } }
      { intros.
        assert (exists vD,
                  exprD' ts tus tvs t0 e = Some vD)
          by (eapply ExprFacts.exprD'_typeof_expr; eauto).
        destruct H6.
        consider (nth_error_get_hlist_nth (typD ts) tus u); intros.
        { destruct s.
          assert (x2 = t0).
          { eapply nth_error_get_hlist_nth_Some in H7. destruct H7.
            clear - H4 x3. simpl in *. congruence. }
          subst.
          eapply HlookupU with (v := u) in H6; eauto.
          forward_reason. eapply ExprFacts.exprD'_typeof_expr.
          eauto. }
        { clear - H4 H7; exfalso.
          eapply nth_error_get_hlist_nth_None in H7. congruence. } } }
    { autorewrite with exprD_rw in *; simpl in *.
      match goal with
        | H : appcontext [ @typ2_match _ _ _ _ _ ?X ?Y ] |- _ =>
          let H := fresh in
          destruct (@typ2_match_case _ _ _ _ _ X Y) as [ [ ? [ ? [ ? H ] ] ] | H ];
            ( try rewrite H in * )
      end; clear H0.
      { unfold Relim in *. red in x1; subst.
        destruct (eq_sym (typ2_cast ts x x0)).
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
        generalize (exprD'_lift ts tus' x1 nil tvex tvs' x); simpl.
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

  Theorem exprD'_subst
  : forall tus tvs tus' tvs' lookupU lookupV P (e : expr typ func) (t : typ),
      (forall u, Natural (lookupU u)) -> (forall v, Natural (lookupV v)) ->
      (forall t e v vD vD_orig,
         nth_error_get_hlist_nth _ tvs v = Some (@existT _ _ t vD) ->
         exprD' ts tus tvs t e = Some vD_orig ->
         exists vD',
           exprD' ts tus' tvs' t (lookupV v _ (fun x => x) e) = Some vD' /\
           forall us vs us' vs',
             P us vs us' vs' ->
             vD_orig us vs = vD vs ->
             vD vs = vD' us' vs') ->
      (forall t e v vD vD_orig,
         nth_error_get_hlist_nth _ tus v = Some (@existT _ _ t vD) ->
         exprD' ts tus tvs t e = Some vD_orig ->
         exists vD',
           exprD' ts tus' tvs' t (lookupU v _ (fun x => x) e) = Some vD' /\
           forall us vs us' vs',
             P us vs us' vs' ->
             vD_orig us vs = vD us ->
             vD us = vD' us' vs') ->
      forall tvx eD,
        exprD' ts tus (tvx ++ tvs) t e = Some eD ->
      exists eD',
        exprD' ts tus' (tvx ++ tvs') t (subst lookupU lookupV (length tvx) e) = Some eD' /\
        forall us vs us' vs' vx,
          P us vs us' vs' ->
          eD us (hlist_app vx vs) = eD' us' (hlist_app vx vs').
  Proof.
    intros.
    eapply (@exprD'_subst' lookupU lookupV tus tvs tus' tvs' P)
      with (tvex := tvx) in H1; eauto.
  Qed.

  Definition mentions (uv : nat + nat) (e : expr typ func) : bool :=
    match uv with
      | inl u => mentionsU u e
      | inr v => mentionsV v e
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
      mentionsV (z + n0 + n) (lift z n x) = mentionsV (z + n0) x.
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

  Theorem mentions_subst
  : forall lookupU lookupV,
      (forall u, Natural (lookupU u)) -> (forall v, Natural (lookupV v)) ->
      forall e uv n,
      let lookup uv :=
          match uv with
            | inl u => lookupU u
            | inr v => lookupV v
          end
      in
      mentions (lift_uv uv n) (subst lookupU lookupV n e) = true <->
      (   (mentions (lift_uv uv n) e = true /\
           forall e',
             mentions uv e' = true ->
             mentions uv (lookup uv _ (fun x => x) e') = true)
       \/ (exists u' e',
             (forall e'',
                lookup u' _ (fun x => x) e'' = e') /\
             mentions (lift_uv u' n) e = true /\
             mentions uv e' = true)).
  Proof.
(*
    induction e; simpl; intros.
    { intros. destruct uv; simpl.
      { rewrite false_eq_true_False.
        setoid_rewrite False_and.
        rewrite False_or.
        split.
        { generalize (lt_rem_sound n v). 
          destruct (lt_rem v n); intros.
          { forward_reason; subst.
            destruct (H0 (v - n)) as [ [ ] | ].
            { rewrite H3 in H2.
              rewrite mentionsU_lift in H2.
              exists (inr (v - n)); eexists; split; eauto. split; auto.
              simpl. eapply EqNat.beq_nat_true_iff.
              omega. }
            { rewrite H3 in *. simpl in *. congruence. } }
          { simpl in *. congruence. } }
        { intros; forward_reason.
          destruct x; simpl in *; try congruence.
          eapply EqNat.beq_nat_true_iff in H2.
          subst.
          generalize (lt_rem_sound n (n1 + n)).
          destruct (lt_rem (n1 + n) n); intros.
          { forward_reason. subst.
            replace (n1 + n - n) with n1 by omega.
            destruct (H0 n1) as [ [] | ].
            { rewrite H4 in *.
              setoid_rewrite H4 in H1.
              specialize (H1 (Var 0)).
              subst. rewrite mentionsU_lift. assumption. }
            { setoid_rewrite H4 in H1.
              exfalso.
              destruct x0; try solve [ specialize (H1 (Var 0)); congruence
                                     | specialize (H1 (UVar 0)); congruence ]. } }
          { exfalso; omega. } } }
      { split; intros.
        { generalize (lt_rem_sound n v).
          destruct (lt_rem v n).
          { intros; forward_reason; subst.
            match goal with
              | |- (?X = true /\ _) \/ _ =>
                consider X; intros
            end.
            { left. split; auto. intros.
              subst.
              replace (n0 + n - n) with n0 in H1 by omega.
              destruct (H0 n0) as [ [] | ]; rewrite H3 in *; auto.
              change (n0 + n) with (0 + n0 + n) in H1.
              rewrite mentionsV_lift in H1. assumption. }
            { right.
              destruct (H0 (v - n)) as [ [] | ].
              { rewrite H4 in H1.
                change (n0 + n) with (0 + n0 + n) in H1.
                rewrite mentionsV_lift in H1.
                exists (inr (v - n)); exists x; simpl.
                replace (v - n + n) with v.
                setoid_rewrite H4. split; auto. split; auto.
                eapply rel_dec_correct. reflexivity.
                clear - H2. rewrite NPeano.Nat.sub_add; auto. }
              { rewrite H4 in H1.
                simpl in H1.
                exfalso. rewrite rel_dec_correct in H1.
                auto. } } }
          { intros. exfalso.
            simpl in H1. rewrite rel_dec_correct in H1.
            subst. omega. } }
        { destruct H1; forward_reason.
          { rewrite rel_dec_correct in H1. subst.
            generalize (lt_rem_sound n (n0 + n)).
            destruct (lt_rem (n0 + n) n).
            { intros; forward_reason.
              assert (n0 = n1) by omega. clear H3. subst.
              destruct (H0 n1) as [ [] | ].
              { rewrite H3.
                setoid_rewrite H3 in H2.
                change (n1 + n) with (0 + n1 + n).
                rewrite mentionsV_lift. eapply H2.
                instantiate (1 := Var n1).
                simpl. rewrite rel_dec_correct. reflexivity. }
              { rewrite H3. simpl.
                rewrite rel_dec_correct. reflexivity. } }
            { intros. exfalso; omega. } }
          { generalize (lt_rem_sound n v).
            destruct (lt_rem v n).
            { intros; forward_reason.
              subst. destruct x; simpl in *; try congruence.
              rewrite rel_dec_correct in H2. subst.
              replace (n1 + n - n) with n1 by omega.
              destruct (H0 n1) as [ [] | ]; rewrite H2.
              { setoid_rewrite H2 in H1.
                change (n0 + n) with (0 + n0 + n).
                rewrite mentionsV_lift. specialize (H1 (Var 0)). subst.
                assumption. }
              { setoid_rewrite H2 in H1.
                destruct x0; try solve [ specialize (H1 (Var 0)); congruence
                                       | specialize (H1 (UVar 0)); congruence ]. } }
            { simpl; intro. exfalso.
              destruct x; simpl in *; try congruence.
              rewrite rel_dec_correct in H2. omega. } } } } }
    { clear. setoid_rewrite mentions_Inj.
      intuition; forward_reason; eauto. }
    { repeat setoid_rewrite mentions_App.
      repeat setoid_rewrite Bool.orb_true_iff.
      rewrite IHe1; clear IHe1.
      rewrite IHe2; clear IHe2.
      rewrite or_rearrange.
      eapply or_iff.
      intuition.
      do 2 setoid_rewrite exists_or.
      do 2 (apply exists_iff; intros).
      rewrite or_factor.
      apply and_iff_compat_l.
      intuition. }
    { setoid_rewrite mentions_Abs.
      destruct uv.
      { generalize (IHe (inl n0)); clear IHe.
        simpl; intro XXX; rewrite XXX; clear XXX.
        split; destruct 1; auto.
        { forward_reason. right.
          exists x. exists x0.
          destruct x; simpl in *; eauto.
          { rewrite <- plus_n_Sm in H2. auto. } }
        { right. forward_reason.
          exists x; exists x0.
          destruct x; simpl in *; eauto.
          { rewrite <- plus_n_Sm. auto. } } }
      { generalize (IHe (inr n0) (S n)).
        simpl. rewrite <- plus_n_Sm.
        intro XXX; rewrite XXX; clear XXX.
        split; destruct 1; forward_reason; eauto.
        { right.
          exists x; exists x0.
          split; auto. split; auto.
          clear - H2. destruct x; simpl in *; auto.
          rewrite plus_n_Sm. assumption. }
        { right.
          exists x; exists x0.
          split; auto. split; auto.
          clear - H2; destruct x; simpl in *; eauto.
          rewrite <- plus_n_Sm; assumption. } } }
    { split; intro.
      { destruct uv; simpl in *.
        { consider (EqNat.beq_nat n0 u); intros; subst.
          { left. split; auto. intros.
            revert H1.
            destruct (H u); forward_reason.
            { do 2 rewrite H1.
              rewrite mentionsU_lift. auto. }
            { do 2 rewrite H1. auto. } }
          { right. destruct (H u); forward_reason.
            { rewrite H3 in *.
              exists (inl u); simpl.
              setoid_rewrite H3.
              rewrite mentionsU_lift in H1.
              eexists; split; eauto.
              rewrite <- EqNat.beq_nat_refl. auto. }
            { rewrite H3 in *.
              exfalso. simpl in *.
              apply EqNat.beq_nat_true in H1. auto. } } }
        { right.
          destruct (H u) as [ [ ] | ].
          { rewrite H2 in *.
            change (n0 + n) with (0 + n0 + n) in H1.
            rewrite mentionsV_lift in H1.
            simpl in *.
            eexists (inl u); exists x; simpl.
            split; [ | split; [ rewrite <- EqNat.beq_nat_refl; auto | eassumption ] ].
            intro. rewrite H2. reflexivity. }
          { rewrite H2 in H1.
            exfalso. simpl in H1. congruence. } } }
      { destruct H1; forward_reason.
        { destruct uv; simpl in *; try congruence.
          apply EqNat.beq_nat_true in H1. subst.
          destruct (H u) as [ [ ] | ].
          { rewrite H1. setoid_rewrite H1 in H2.
            rewrite mentionsU_lift. eapply H2.
            instantiate (1 := UVar u). simpl.
            rewrite <- EqNat.beq_nat_refl. auto. }
          { rewrite H1. simpl.
            rewrite <- EqNat.beq_nat_refl. auto. } }
        { destruct x; simpl in *; try congruence.
          apply EqNat.beq_nat_true in H2. subst.
          destruct (H u) as [ [ ] | ].
          { rewrite H2.
            setoid_rewrite H2 in H1.
            specialize (H1 x0). subst.
            destruct uv; simpl.
            { rewrite mentionsU_lift. auto. }
            { simpl in *.
              change (n0 + n) with (0 + n0 + n).
              rewrite mentionsV_lift. assumption. } }
          { setoid_rewrite H2 in H1.
            clear - H1. exfalso.
            destruct x0; try solve [ specialize (H1 (Var 0)); congruence
                                   | specialize (H1 (UVar 0)); congruence ]. } } } }
*)
  Abort.

End substitute.