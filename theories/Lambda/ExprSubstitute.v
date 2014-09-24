(** This file contains generic functions for manipulating,
 ** (i.e. substituting and finding) unification variables
 **)
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Traversable.
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

(** The key insight of this file is that it handles semantic/logical
 ** relations.
 ** This allows us to factor out the common pieces.
 **)

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

  Variable m : Type -> Type.
  Variable Monad_m : Monad m.
  Variable lookupU : uvar -> list (expr typ func) -> m (expr typ func).
  Variable lookupV : var -> m (expr typ func).

  Fixpoint subst' (lift_by : nat) (e : expr typ func) {struct e}
  : m (expr typ func) :=
    match e with
      | Var v => match lt_rem v lift_by with
                   | None => pure (Var v)
                   | Some diff =>
                     fmap (lift 0 lift_by) (lookupV diff)
                 end
      | Inj _ => pure e
      | UVar u es =>
        (* the issue is that [es] is meaningless to [lookupU] because
         * [es] could mention variables that do not exist in the context that
         * [lookupU] reasons about.
         * >> The purpose of the extra terms is to enable contexts, they
         *    should not mention anything that doesn't make sense for the
         *    top unification variable.
         * >> But they could, e.g.
         *       \ x (pf : x = y) . ?0 [y]
         *    could become
         *       \ x (pf : x = y) . ?0 [x]
         *    the key thing to note is that these things are "equal"
         *    and the bottom term was really constructed via a term.
         * >> The way to solve this is to offer the context to the
         *    function and ensure that it knows how to construct the
         *    final result.
         *)
        bind (m := m) (mapT_list (subst' lift_by) es) (lookupU u)
      | App l r => ap (ap (pure App) (subst' lift_by l)) (subst' lift_by r)
      | Abs t e => fmap (Abs t) (subst' (S lift_by) e)
    end.

  Definition subst (under : nat) (e : expr typ func)
  : m (expr typ func) :=
    subst' under e.

  Variable RType_typ : RType typ.
  Variable Typ2_Fun : Typ2 _ Fun.
  Context {RSym_func : RSym func}.

  (** Reasoning principles **)
  Context {RTypeOk_typD : RTypeOk}.
  Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.
  Context {RSymOk_func : RSymOk RSym_func}.
(*
  Lemma typeof_expr_subst'
  : forall tus tus' e tvs tvs'
           (HlookupV : forall v t e',
                         lookupV v = pure e' ->
                         nth_error tvs v = Some t ->
                         typeof_expr tus' tvs' e' = Some t)
           (HlookupU : forall u t e' es,
                         lookupU u es = pure e' ->
                         nth_error tus u = Some t ->
                         Forall2 (fun t e => typeof_expr tus' tvs' e = Some t) t.(cctx) es ->
                         typeof_expr tus' tvs' e' = Some t.(vtyp))
      y tvex e',
      typeof_expr tus (tvex ++ tvs) e = Some y ->
      subst' (length tvex) e = ret e' ->
      typeof_expr tus' (tvex ++ tvs') e' = Some y.
  Proof.
    intros tus tus' tvs tvs' HlookupV HlookupU.
    Print ExprD.ExprFacts.



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
  Admitted.
*)

  (** TODO: Move this, duplicated **)
  Inductive Forall5 {A B} {C : A -> Type} {D} {E : A -> Type}
            (P : forall x : A, B -> C x -> D -> E x -> Prop)
  : forall ls : list A, list B -> hlist C ls -> list D -> hlist E ls -> Prop :=
  | Forall5_nil : @Forall5 A B C D E P nil nil Hnil nil Hnil
  | Forall5_cons : forall t ts x xs y ys z zs b bs,
                     @P t x y z b ->
                     @Forall5 A B C D E P ts xs ys zs bs->
                     @Forall5 A B C D E P (t :: ts) (x :: xs) (Hcons y ys) (z :: zs) (Hcons b bs).

  Lemma bind_ret : forall {A B} (c : m A) (f : A -> m B) x,
                     bind c f = ret x ->
                     exists c', c = ret c' /\
                                f c' = ret x.
  Proof. clear.
  Admitted.
  Lemma ret_ret : forall {A} (a b : A),
                    ret (m:=m) a = ret b -> a = b.
  Proof.
  Admitted.

  Lemma fmap_ret : forall {A B : Type} (f : A -> B) x y,
                     fmap (F:=m) f x = ret y ->
                     exists x', x = ret x' /\ f x' = y.
  Proof.
    clear.
    simpl. unfold liftM.
    intros. eapply bind_ret in H.
    forward_reason.
    eexists; split; eauto.
    eapply ret_ret in H0.
    assumption.
  Qed.

  Lemma pure_is_ret : forall T (a b : T), pure a = ret (m:=m) b -> a = b.
  Proof.
    clear.
    simpl. intros. apply ret_ret. assumption.
  Qed.

  Lemma ap_ret : forall T U (f : m (T -> U)) x y,
                   ap f x = ret y ->
                   exists x' f', x = ret x' /\
                                 f = ret f' /\
                                 y = f' x'.
  Proof.
    clear; simpl.
    unfold apM, liftM.
    intros.
    eapply bind_ret in H; forward_reason.
    eapply bind_ret in H0; forward_reason.
    eapply ret_ret in H1. eauto.
  Qed.

  Theorem exprD'_subst'
  : forall (tus : tenv (ctyp typ)) tvs tus' tvs'
           (P : exprT tus tvs (exprT tus' tvs' Prop))
      (HlookupV : forall t e' v vD,
         lookupV v = ret e' ->
         nth_error_get_hlist_nth _ tvs v = Some (@existT _ _ t vD) ->
         exists vD',
           exprD' tus' tvs' t e' = Some vD' /\
           forall us vs us' vs',
             P us vs us' vs' ->
             vD vs = vD' us' vs')
      (HlookupU : forall t es e' u vD vals es' vals',
         lookupU u es = ret e' ->
         nth_error_get_hlist_nth _ tus u = Some (@existT _ _ t vD) ->
         @Forall5 typ
                  (expr typ func) (fun t => exprT tus tvs (typD t))
                  (expr typ func) (fun t => exprT tus' tvs' (typD t))
                  (fun t e v e' v' =>
                    exprD' tus tvs t e = Some v /\
                    exprD' tus' tvs' t e = Some v' /\
                    forall us vs us' vs',
                      v us vs = v' us' vs') t.(cctx) es vals es' vals' ->
         exists (vD' : exprT tus' tvs' (typD t.(vtyp))),
           exprD' tus' tvs' t.(vtyp) e' = Some vD' /\
           forall (us : hlist ctxD tus) vs
                  (us' : hlist ctxD tus') vs',
             P us vs us' vs' ->
             vD us (hlist_map (F:=fun t => exprT tus tvs (typD t)) (fun t x => x us vs) vals) = vD' us' vs'),
      forall e e' tvex (t : typ) eD,
        subst' (length tvex) e = ret e' ->
        exprD' tus (tvex ++ tvs) t e = Some eD ->
        exists eD',
          exprD' tus' (tvex ++ tvs') t e' = Some eD' /\
          forall us vs us' vs' vex,
            P us vs us' vs' ->
            eD us (hlist_app vex vs) = eD' us' (hlist_app vex vs').
  Proof.
    induction e; simpl; intros.
    { clear HlookupU.
      generalize (lt_rem_sound (length tvex) v).
      destruct (lt_rem v (length tvex)).
      { destruct 1.
        autorewrite with exprD_rw in H0; simpl in H0.
        forwardy; inv_all; subst.
        destruct y.
        eapply nth_error_get_hlist_nth_appR in H0; eauto.
        simpl in *. forward_reason.
        eapply fmap_ret in H. destruct H as [ ? [ ? ? ] ].
        eapply HlookupV in H; eauto.
        forward_reason.
        generalize (exprD'_lift tus' x1 nil tvex tvs' x).
        change_rewrite H. simpl.
        intros; forwardy.
        subst.
        eexists; split; try eassumption.
        intros.
        unfold Rcast_val, Rcast, Relim. simpl.
        rewrite H2; clear H2.
        specialize (H7 us' Hnil vex vs'). simpl in H7.
        rewrite <- H7. eapply H5; eauto. }
      { eapply pure_is_ret in H. subst.
        autorewrite with exprD_rw in H0; simpl in H0.
        forwardy; inv_all; subst.
        destruct y.
        autorewrite with exprD_rw; simpl.
        intro.
        destruct (@nth_error_get_hlist_nth_appL _ typD tvs' tvex _ H1).
        destruct (@nth_error_get_hlist_nth_appL _ typD tvs tvex _ H1).
        rewrite H in *.
        forward_reason; inv_all; subst.
        simpl in *.
        rewrite H2.
        destruct x0. simpl in *.
        rewrite H6 in H4.
        inv_all. subst.
        rewrite H0.
        eexists; split; eauto.
        intros.
        unfold Rcast_val, Rcast; simpl.
        rewrite H5; clear H5.
        rewrite H7; clear H7. reflexivity. } }
    { eapply pure_is_ret in H.
      subst.
      revert H0.
      autorewrite with exprD_rw. simpl.
      destruct (funcAs f0 t); try congruence.
      eexists; split; eauto.
      inv_all; subst.
      auto. }
    { eapply ap_ret in H.
      forward_reason.
      eapply ap_ret in H1.
      forward_reason.
      subst.
      apply pure_is_ret in H3. subst.
      revert H0.
      autorewrite with exprD_rw; simpl.
      intros. forwardy; inv_all; subst.
      specialize (IHe1 _ _ _ _ H1 H2); clear H1 H2.
      specialize (IHe2 _ _ _ _ H H3); clear H H3.
      forward_reason.
      rewrite (ExprTac.exprD_typeof_Some _ _ _ _ _ H).
      rewrite H. rewrite H1.
      eexists; split; eauto.
      intros.
      unfold exprT_App.
      clear - H2 H3 H4.
      unfold exprT, OpenT.OpenT.
      autorewrite with eq_rw.
      erewrite H3; eauto.
      erewrite H2; eauto. }
    { clear HlookupU HlookupV.
      eapply fmap_ret in H.
      destruct H as [ ? [ ? ? ] ].
      subst.
      revert H0.
      autorewrite with exprD_rw; simpl.
      intros.
      ExprTac.arrow_case_any.
      { forward_reason.
        red in x2. subst.
        simpl in *.
        revert H0.
        autorewrite with eq_rw.
        destruct (type_cast x0 t); try congruence.
        intros. forward; inv_all; subst.
        specialize (IHe _ (t :: tvex) x1 _ H H0).
        forward_reason.
        simpl in *. rewrite H2.
        eexists; split; eauto.
        intros.
        unfold exprT, OpenT.OpenT.
        autorewrite with eq_rw.
        eapply Eq.match_eq_match_eq with (F:=fun x=>x).
        eapply functional_extensionality.
        intros. eapply (H3 us vs us' vs' (Hcons (Rcast_val r x3) vex)); auto. }
      { congruence. } }
    { revert H1.
      eapply bind_ret in H0.
      forward_reason.
      clear HlookupV.
      autorewrite with exprD_rw; simpl.
      intros. forwardy.
      inv_all; subst.
      specialize (fun vals vals' => @HlookupU x0 x e' u _ vals l vals' H1 H2).
      admit. }
  Qed.

  Theorem exprD'_subst
  : forall (tus : tenv (ctyp typ)) tvs tus' tvs'
           (P : exprT tus tvs (exprT tus' tvs' Prop))
      (HlookupV : forall t e' v vD,
         lookupV v = ret e' ->
         nth_error_get_hlist_nth _ tvs v = Some (@existT _ _ t vD) ->
         exists vD',
           exprD' tus' tvs' t e' = Some vD' /\
           forall us vs us' vs',
             P us vs us' vs' ->
             vD vs = vD' us' vs')
      (HlookupU : forall t es e' u vD vals es' vals',
         lookupU u es = ret e' ->
         nth_error_get_hlist_nth _ tus u = Some (@existT _ _ t vD) ->
         @Forall5 typ
                  (expr typ func) (fun t => exprT tus tvs (typD t))
                  (expr typ func) (fun t => exprT tus' tvs' (typD t))
                  (fun t e v e' v' =>
                    exprD' tus tvs t e = Some v /\
                    exprD' tus' tvs' t e = Some v' /\
                    forall us vs us' vs',
                      v us vs = v' us' vs') t.(cctx) es vals es' vals' ->
         exists (vD' : exprT tus' tvs' (typD t.(vtyp))),
           exprD' tus' tvs' t.(vtyp) e' = Some vD' /\
           forall (us : hlist ctxD tus) vs
                  (us' : hlist ctxD tus') vs',
             P us vs us' vs' ->
             vD us (hlist_map (F:=fun t => exprT tus tvs (typD t)) (fun t x => x us vs) vals) = vD' us' vs'),
      forall e e' tvex (t : typ) eD,
        subst (length tvex) e = ret e' ->
        exprD' tus (tvex ++ tvs) t e = Some eD ->
        exists eD',
          exprD' tus' (tvex ++ tvs') t e' = Some eD' /\
          forall us vs us' vs' vex,
            P us vs us' vs' ->
            eD us (hlist_app vex vs) = eD' us' (hlist_app vex vs').
  Proof.
    eapply exprD'_subst'.
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
    { Lemma existsb_map : forall T U (f : T -> U) P ls,
                            existsb P (map f ls) = existsb (fun x => P (f x)) ls.
      Proof.
        clear. induction ls; simpl; auto.
        rewrite IHls. reflexivity.
      Qed.
      rewrite existsb_map.
      clear - H.
      induction H; simpl; auto.
      rewrite H. rewrite IHForall. reflexivity. }
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

(*
  Theorem mentions_subst
  : forall lookupU lookupV,
      forall e uv n,
      let lookup uv :=
          match uv with
            | inl u => lookupU u
            | inr v => lookupV v
          end
      in
      mentions (lift_uv uv n) (subst n e) = true <->
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
*)

End substitute.