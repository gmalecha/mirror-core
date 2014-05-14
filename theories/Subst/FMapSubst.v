Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Bool.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SymI.
(** TODO: These should be abstracted **)
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.ExprLift.
Require Import MirrorCore.Ext.ExprSubst.

Set Implicit Arguments.
Set Strict Implicit.

(** Temporary **)
Require Import FunctionalExtensionality.

(** Finite Maps **) 
Require Import FMapInterface.

Module Make (FM : S with Definition E.t := uvar
                    with Definition E.eq := @eq uvar).

  Require FMapFacts.

  Module FACTS := FMapFacts.WFacts FM.
  Module PROPS := FMapFacts.WProperties FM.

  Section hide_hints.
    Variable ts : types.
    Variable func : Type.
    Variable RSym_func : RSym (typD ts) func.

    Definition raw : Type := FM.t (expr func).

    Definition normalized (this : raw) (e : expr func) : Prop :=
      forall u, mentionsU u e = true -> ~FM.In u this.

    Definition WellFormed (this : raw) : Prop :=
      forall (k : uvar) e,
        FM.MapsTo k e this ->
        normalized this e.

    Definition raw_lookup : uvar -> raw -> option (expr func) :=
       @FM.find _.

    (** this is like instantiate **)
    Section raw_subst.
      Variable s : raw.

      Fixpoint raw_subst (under : nat) (e : expr func) : expr func :=
        match e with
          | Var _
          | Inj _ => e
          | App l r => App (raw_subst under l) (raw_subst under r)
          | Abs t e => Abs t (raw_subst (S under) e)
          | UVar u =>
            match raw_lookup u s with
              | None => e
              | Some e => lift 0 under e
            (** 0 should be the number of binders to skip
             **)
            end
        end.
    End raw_subst.

    Definition raw_set (u : uvar) (e : expr func) (s : raw) : option raw :=
      let v' := raw_subst s 0 e in
      if mentionsU u v'
      then None
      else let s := FM.add u v' s in
           let s := FM.map (raw_subst s 0) s in
           Some s.

    Definition raw_WellTyped (U G : EnvI.tenv _) (s : raw) : Prop :=
      forall k v, FM.MapsTo k v s ->
        exists t, nth_error U k = Some t /\ WellTyped_expr U G v t.

    Lemma raw_lookup_MapsTo : forall u s e,
                                raw_lookup u s = Some e <-> FM.MapsTo u e s.
    Proof.
      intros. split; intro.
      eapply FM.find_2 in H. auto.
      eapply FM.find_1; eauto.
    Qed.
    Lemma raw_lookup_In : forall u s,
                            raw_lookup u s = None <-> ~FM.In u s.
    Proof.
      unfold raw_lookup; intros.
      rewrite PROPS.F.not_find_in_iff. intuition.
    Qed.
    Hint Resolve -> raw_lookup_MapsTo.
    Hint Resolve -> raw_lookup_In.

    Lemma normalized_lift : forall s n e,
                              normalized s e <-> normalized s (lift 0 n e).
    Proof.
      unfold normalized. intuition.
      rewrite mentionsU_lift in *. eauto.
      eapply H. rewrite mentionsU_lift; eauto. eauto.
    Qed.

    Lemma mentionsU_raw_subst_n_irr : forall u s e n n',
      mentionsU u (raw_subst s n e) = mentionsU u (raw_subst s n' e).
    Proof.
      induction e; simpl; intros; auto.
      { rewrite (IHe1 n n'). rewrite (IHe2 n n'). auto. }
      { destruct (raw_lookup u0 s); auto.
        repeat rewrite mentionsU_lift. auto. }
    Qed.

    Lemma wf_instantiate_normalized : forall s e n,
      WellFormed s ->
      normalized s (raw_subst s n e).
    Proof.
      unfold WellFormed; intros. induction e; simpl in *; intros; red; simpl; intuition.
      { consider (mentionsU u (raw_subst s n e1)); intros.
        eapply IHe1 in H0; auto.
        eapply IHe2 in H2; auto. }
      { destruct H1. specialize (H _ _ H1).
        specialize (IHe u). eapply IHe.
        2: exists x; eauto.
        erewrite mentionsU_raw_subst_n_irr with (n' := n) in H0.
        eauto. }
      { consider (raw_lookup u s); intros.
        { eapply raw_lookup_MapsTo in H0.
          eapply H in H0.
          rewrite mentionsU_lift in *.
          eapply H0 in H2. auto. }
        { simpl in *. consider (EqNat.beq_nat u0 u); intros.
          subst. eapply raw_lookup_In in H0. auto. } }
    Qed.

    Local Ltac think :=
      unfold raw_lookup in *; simpl in *; intros;
      repeat (match goal with
                | [ H : _ && _ = true |- _ ] =>
                  apply andb_true_iff in H; destruct H
                | [ H : _ || _ = false |- _ ] =>
                  apply orb_false_iff in H; destruct H
                | [ H : _ |- _ ] =>
                  rewrite H in * by auto
                | [ H : Some _ = Some _ |- _ ] =>
                  inversion H; clear H; subst
                | [ H : context [ if ?X then _ else _ ] |- _ ] =>
                  consider X; intros; (solve [ try congruence ] || (try congruence; [ ]))
                | [ |- context [ if ?X then _ else _ ] ] =>
                  consider X; intros; (solve [ try congruence ] || (try congruence; [ ]))
                | [ H : ?X = ?X |- _ ] => clear H
                | [ |- _ ] => progress ( simpl in * )
              end
              || rewrite FACTS.add_o in *
              || rewrite FACTS.map_o in *
              || rewrite FACTS.remove_o in * ); try congruence.

    Ltac reducer :=
      unfold raw_lookup ;
      repeat (   (rewrite FACTS.add_eq_o by intuition)
              || (rewrite FACTS.add_neq_o by intuition)).

    Lemma raw_subst_add_not_mentions : forall k e e' s n,
      mentionsU k e = false ->
      raw_subst (FM.add k e' s) n  e = raw_subst s n e.
    Proof.
      induction e; simpl; intros; intuition;
      repeat match goal with
               | _ : match ?X with _ => _ end = _ |- _ =>
                 consider X; try congruence; intros
             end;
      try solve [ f_equal; eauto ].
      { consider (EqNat.beq_nat k u); try congruence; intros.
        reducer. auto. }
    Qed.

    Definition raw_substD us vs (sub : raw) : Prop :=
      FM.fold (fun k v P =>
                 match nth_error us k with
                   | None => False
                   | Some (existT T val) => match exprD us vs v T with
                                              | Some val' => val = val' /\ P
                                              | None => False
                                            end
                 end) sub True.

    Record subst : Type :=
    { env : raw
    ; wf : WellFormed env
    }.

    Definition subst_lookup (uv : uvar) (s : subst) : option (expr func) :=
      raw_lookup uv s.(env).

    Definition subst_subst (s : subst) : nat -> expr func -> expr func :=
      raw_subst s.(env).

    Theorem MapsTo_map_add : forall T U k (v : T) f k' (v' : U) m,
      FM.MapsTo k v (FM.map f (FM.add k' v' m)) <->
      FM.MapsTo k v (FM.add k' (f v') (FM.map f m)).
    Proof.
      intros. rewrite FACTS.map_mapsto_iff.
      repeat rewrite FACTS.add_mapsto_iff.
      split; intros.
      { destruct H. intuition. subst.
        eapply FACTS.add_mapsto_iff in H1.
        intuition. subst. eauto. }
      { intuition; subst.
        exists v'. intuition.
        rewrite FACTS.map_mapsto_iff in H1. destruct H1.
        intuition. subst. exists x. intuition. }
    Qed.

    Lemma normalized_App : forall s l r,
      normalized s (App l r) <-> (normalized s l /\ normalized s r).
    Proof.
      intuition.
      { red; intros. specialize (H u); simpl in *.
        rewrite H0 in *. eauto. }
      { red; intros. specialize (H u); simpl in *.
        rewrite H0 in *. destruct (mentionsU u l); auto. }
      { red; simpl; intros.
        consider (mentionsU u l).
        { intro X; specialize (H0 _ X); auto. }
        { intros ? X; specialize (H1 _ X); auto. } }
    Qed.

    Lemma raw_subst_normalized : forall r e n,
      normalized r e ->
      raw_subst r n e = e.
    Proof.
      induction e; simpl; intros;
      try (rewrite normalized_App in * || rewrite normalized_Equal in * );
      repeat match goal with
               | H : _ |- _ => erewrite H by intuition
             end; auto.
      red in H; simpl in *. specialize (H u).
      consider (raw_lookup u r); auto; intros.
      exfalso. eapply H.
      2: exists e; eauto.
      consider (EqNat.beq_nat u u); auto.
    Qed.

    Lemma raw_subst_idem : forall e b c d,
      WellFormed c ->
      raw_subst c b (raw_subst c d e) = raw_subst c d e.
    Proof.
      intros.
      erewrite raw_subst_normalized; auto using wf_instantiate_normalized.
    Qed.

    Lemma mentionsU_add_normalized : forall u e s x n,
      normalized s x ->
      raw_subst (FM.add u e s) n x =
      raw_subst (FM.add u e (FM.empty _)) n x.
    Proof.
      induction x; simpl; intros;
      repeat match goal with
               | H : _ |- _ => rewrite H
             end; auto.
      { apply normalized_App in H. intuition. }
      { apply normalized_App in H. intuition. }
      { unfold raw_lookup.
        repeat rewrite FACTS.add_o.
        destruct (FM.E.eq_dec u u0); auto.
        rewrite FACTS.empty_o.
        consider (FM.find u0 s); auto.
        intros. exfalso. eapply H.
        instantiate (1 := u0). simpl.
        consider (EqNat.beq_nat u0 u0); try congruence.
        exists e0. eauto. }
    Qed.

    Ltac go :=
      repeat match goal with
               | H : exists x, _ |- _ =>
                 destruct H
             end.

    Lemma mentionsU_subst : forall s u x n,
      mentionsU u (raw_subst s n x) = true <->
      (mentionsU u x = true /\ ~FM.In u s \/
                               exists u' e',
                                 FM.MapsTo u' e' s /\
                                 mentionsU u' x = true /\
                                 mentionsU u e' = true).
    Proof.
      induction x; simpl; intros;
      try solve [intuition; go; intuition; auto ].
      { specialize (IHx1 n); specialize (IHx2 n).
        consider (mentionsU u (raw_subst s n x1)); intros.
        { rewrite H0.
          intuition; go; intuition repeat match goal with
                                            | H : _ |- _ =>
                                              rewrite H by eauto
                                          end; eauto.
          right. exists x3. eexists; split; eauto. rewrite H0. auto. }
        { consider (mentionsU u (raw_subst s n x2)); intros.
          { intuition; go; intuition repeat match goal with
                                              | H : _ |- _ =>
                                                rewrite H by eauto
                                            end; eauto.
            { destruct (mentionsU u x1); intros; left; split; auto. }
            { right. exists x. rewrite H0. eexists; intuition eauto.
              destruct (mentionsU x x1); auto. } }
          { intuition.
            { consider (mentionsU u x1); intros; eauto. }
            { go. intuition.
              consider (mentionsU x x1); intros.
              { eapply H6. do 2 eexists; eauto. }
              { eapply H7. do 2 eexists; eauto. } } } } }
      { rewrite IHx. intuition. }
      { consider (raw_lookup u0 s); intros.
        { rewrite mentionsU_lift. intuition.
          { right. exists u0; exists e.
            intuition. consider (EqNat.beq_nat u0 u0); congruence. }
          { consider (EqNat.beq_nat u u0); try congruence; intros; subst.
            exfalso. apply H2. exists e; eauto. }
          { destruct H1. destruct H0. intuition.
            consider (EqNat.beq_nat x u0); try congruence; intros; subst.
            apply raw_lookup_MapsTo in H1. rewrite H1 in H.
            inv_all; subst; auto. } }
        { apply raw_lookup_In in H. simpl.
          consider (EqNat.beq_nat u u0); intros; subst; intuition.
          { destruct H2. destruct H1. intuition.
            consider (EqNat.beq_nat x u0); intros; subst.
            exfalso. apply H. exists x0; eauto. } } }
    Qed.

    Theorem raw_set_WellFormed : forall u e s s',
      raw_set u e s = Some s' ->
      WellFormed s ->
      WellFormed s'.
    Proof.
      unfold raw_set; intros.
      consider (mentionsU u (raw_subst s 0 e)); try congruence; intros.
      inv_all; subst.
      red in H0. red. intros.
      rewrite MapsTo_map_add in H1.
      rewrite FACTS.add_mapsto_iff in H1.
      red. intros. intro. destruct H3.
      rewrite MapsTo_map_add in H3.
      rewrite FACTS.add_mapsto_iff in H3.
      intuition; subst; subst.
      { rewrite raw_subst_add_not_mentions in H2; eauto.
        rewrite raw_subst_idem in H2; eauto. congruence. }
      { rewrite raw_subst_add_not_mentions in H2; eauto.
        rewrite FACTS.map_mapsto_iff in H6. destruct H6.
        intuition subst. rewrite raw_subst_idem in H2; eauto.
        assert (normalized s (raw_subst s 0 e)).
        { eapply wf_instantiate_normalized. red. eapply H0. }
        eapply H1. 2: exists x0; eauto. eauto. }
      { rewrite FACTS.map_mapsto_iff in H5. destruct H5; intuition subst.
        eapply H0 in H5.
        rewrite mentionsU_add_normalized in H2; auto.
        rewrite mentionsU_subst in H2.
        intuition; go.
        { apply H4. eexists. eapply FM.add_1. reflexivity. }
        { intuition. eapply FACTS.add_mapsto_iff in H3. intuition.
          { subst. congruence. }
          { generalize (@FM.empty_1 (expr func)).
            intro. red in H4. eapply H4. eauto. } } }
      { rewrite FACTS.map_mapsto_iff in H5.
        rewrite FACTS.map_mapsto_iff in H6.
        destruct H5; destruct H6; intuition subst.
        rewrite mentionsU_add_normalized in H2 by eauto.
        apply mentionsU_subst in H2.
        intuition.
        { eapply H0. 2: eauto. eauto. exists x1; eauto. }
        { go. intuition.
          apply FACTS.add_mapsto_iff in H4. intuition subst.
          { clear - H6 H8 H0.
            generalize (@wf_instantiate_normalized s e 0 H0); intros.
            eapply H in H6. apply H6. eexists; eauto. }
          { apply FACTS.empty_mapsto_iff in H9. auto. } } }
    Qed.

    Definition subst_set (u : uvar) (e : expr func) (s : subst) : option subst :=
      match raw_set u e s.(env) as v return raw_set u e s.(env) = v -> option subst with
        | None => fun _ => None
        | Some s' => fun pf => Some {| env := s'
                                     ; wf := @raw_set_WellFormed _ _ _ _ pf s.(wf) |}
      end eq_refl.

    Definition subst_substD us vs (sub : subst) : Prop :=
      raw_substD us vs sub.(env).

    Definition subst_WellTyped tus tvs (sub : subst) : Prop :=
      raw_WellTyped tus tvs sub.(env).

    Lemma wf_empty : WellFormed (FM.empty (expr func)).
    Proof.
      red. red. intros.
      intro.
      apply FACTS.empty_in_iff in H1. auto.
    Qed.

    Definition subst_empty : subst :=
    {| env := FM.empty _ ; wf := wf_empty |}.

    Instance Subst_subst : Subst subst (expr func) :=
    { lookup := subst_lookup
    ; set := subst_set
    ; empty := subst_empty
    }.

    Section semantic.

      Lemma raw_substD_sem : forall (us vs : EnvI.env (typD ts)) s,
        raw_substD us vs s <->
        (forall uv e,
           raw_lookup uv s = Some e ->
           exists v,
             nth_error us uv = Some v /\
             exprD us vs e (projT1 v) = Some (projT2 v)).
      Proof.
        simpl.
        unfold raw_substD, raw_lookup.
        simpl in *. intros us vs s.
        cut True; auto. generalize True. intro.
        eapply PROPS.map_induction with (m := s); intros.
        { split; intros.
          { eapply FM.find_2 in H2. eapply H in H2. intuition. }
          { rewrite PROPS.fold_Empty; eauto with typeclass_instances. } }
        { split; intros.
          { rewrite PROPS.fold_Add in H3; eauto with typeclass_instances.
            repeat match goal with
                     | H : match ?X with _ => _ end |- _ =>
                       consider X; intros; try contradiction
                     | H : _ /\ _ |- _ => destruct H
                   end; subst.
            rewrite H1 in H4. rewrite FACTS.add_o in H4.
            destruct (FM.E.eq_dec x uv); unfold FM.E.eq in *; subst.
            { rewrite H5. eexists. split; eauto.
              inv_all; subst. simpl. eauto. }
            { eapply H; eauto. }
            { repeat (red; intros; subst);
              repeat match goal with
                       | |- context [ match ?X with _ => _ end ] => destruct X
                     end; intuition. }
            { repeat (red; intros; subst);
              repeat match goal with
                       | |- context [ match ?X with _ => _ end ] => destruct X
                     end; intuition. } }
          { specialize (H H2).
            rewrite PROPS.fold_Add; eauto with typeclass_instances.
            generalize (H3 x e); intros. rewrite H1 in H4. rewrite FACTS.add_o in H4.
            destruct (FM.E.eq_dec x x); try congruence. specialize (H4 refl_equal).
            destruct H4; intuition. rewrite H5.
            destruct x0; simpl in *.
            rewrite H6.
            split; auto.
            eapply H7. intros. eapply H3. rewrite H1.
            rewrite FACTS.add_o.
            destruct (FM.E.eq_dec x uv);
              unfold FM.E.eq in *; auto. subst. exfalso. apply H0.
            exists e1. apply FACTS.find_mapsto_iff; auto.
            { repeat (red; intros; subst);
              repeat match goal with
                       | |- context [ match ?X with _ => _ end ] => destruct X
                     end; intuition. }
            { repeat (red; intros; subst);
              repeat match goal with
                       | |- context [ match ?X with _ => _ end ] => destruct X
                     end; intuition. } } }
      Qed.

      Theorem substD_sem : forall (us vs : EnvI.env (typD ts)) (s : subst),
        subst_substD us vs s <->
        (forall uv e,
           lookup uv s = Some e ->
           exists v,
             nth_error us uv = Some v /\
             exprD us vs e (projT1 v) = Some (projT2 v)).
      Proof.
        destruct s; simpl.
        unfold subst_substD, subst_lookup.
        simpl in *. eauto using raw_substD_sem.
      Qed.

      Lemma raw_subst_typeof : forall u e v v' s,
        raw_WellTyped u v s ->
        typeof_expr u (v' ++ v) (raw_subst s (length v') e) =
        typeof_expr u (v' ++ v) e.
      Proof.
        induction e; simpl; intros;
        repeat match goal with
                 | H : _ |- _ =>
                   rewrite H by eauto
               end; eauto.
        { change (t :: v' ++ v) with ((t :: v') ++ v).
          change (S (length v')) with (length (t :: v')).
          rewrite IHe; eauto. }
        { consider (raw_lookup u0 s); intros.
          red in H. edestruct H; eauto with typeclass_instances.
          intuition. unfold WellTyped_expr in *.
          rewrite (typeof_expr_lift _ u nil v' v).
          simpl; auto. etransitivity; eauto.
          reflexivity. }
      Qed.

      Lemma subst_subst_typeof : forall u e v v' s,
        subst_WellTyped u v s ->
        typeof_expr u (v' ++ v) (subst_subst s (length v') e) =
        typeof_expr u (v' ++ v) e.
      Proof.
        unfold subst_WellTyped, subst_subst. destruct s; simpl.
        auto using raw_subst_typeof.
      Qed.

      Global Instance Injective_typ_cast_typ_hetero_Some ts a b c p :
        Injective (typ_cast_typ ts a b c = Some p) :=
        { result := exists pf : b = c,
                      (fun F => match pf in _ = t
                                      return F (typD ts a b) -> F (typD ts a t)
                                with
                                  | eq_refl => fun x => x
                                end) = p }.
      Proof.
        abstract (intros; exists (typ_cast_typ_eq _ _ _ _ H);
        uip_all;
        subst; rewrite typ_cast_typ_refl in H; f_equal; inv_all; auto).
      Defined.

      Hint Extern 1 (Injective (@typ_cast_typ ?ts ?F ?env ?a ?b = Some ?c)) =>
      exact (@Injective_typ_cast_typ_hetero_Some ts F env a b c) : typeclass_instances.

      Lemma substD_subst_lem : forall u v' s e t,
        subst_substD u v' s ->
        forall v,
          let (tv',vs') := EnvI.split_env v' in
          let (tu,us) := EnvI.split_env u in
          match exprD' tu (v ++ tv') e t ,
                exprD' tu (v ++ tv') (subst_subst s (length v) e) t
          with
            | Some l , Some r => forall vs,
                                   l us (hlist_app vs vs') = r us (hlist_app vs vs')
            | None , None => True
            | _ , _ => False
          end.
      Proof.
(*
        simpl. intros; rewrite substD_sem in *.
        unfold exprD in *.
        destruct (EnvI.split_env v').
        revert t v. induction e; simpl; intros; auto; autorewrite with exprD_rw.
        { match goal with
            | |- match ?X with _ => _ end =>
              destruct X; intros; auto
          end. }
        { forward. }
        { rewrite subst_subst_typeof.
          { destruct (typeof_expr (EnvI.typeof_env u) (v ++ x) e1); auto.
            destruct t0; auto.
            specialize (IHe1 (tyArr t0_1 t0_2) v).
            specialize (IHe2 t0_1 v).
            simpl in *.
            repeat match goal with
                     | |- context [ @ExprD.exprD' ?A ?B ?C ?D ?E ?F ?G ] =>
                       consider (@ExprD.exprD' A B C D E F G); intros
                   end; intuition try congruence; auto.
            destruct (typ_cast_typ ts nil t0_2 t); auto.
            intros. rewrite IHe2. rewrite IHe1. auto. }
          { clear IHe1 IHe2.
            red. red. intros.
            simpl in *. unfold subst_lookup, raw_lookup in *.
            destruct (H k v0). eapply FM.find_1. auto.
            intuition.
            consider (ExprD.exprD' u x v0 (projT1 x0)); intros; try congruence.
            inv_all; subst.
            destruct x0. simpl in *. subst.
            exists x0.
            rewrite nth_error_typeof_env. rewrite H2. simpl.
            split; auto.
            eapply ExprD.typeof_expr_exprD'.
            eauto. } }
        { destruct t0; auto.
          destruct (typ_cast_typ ts nil t0_1 t); auto.
          specialize (IHe t0_2 (t :: v)).
          simpl in *.
          change (S (length v)) with (length (t :: v)) in *.
          repeat match goal with
                   | |- context [ @ExprD.exprD' ?A ?B ?C ?D ?E ?F ?G ] =>
                     consider (@ExprD.exprD' A B C D E F G); intros
                 end; try congruence; eauto.
          eapply functional_extensionality. intros.
          specialize (IHe (Hcons (F := typD ts nil) (p (fun x => x) x0) vs)).
          simpl in *. auto. }
        { simpl in *.
          unfold raw_lookup, EnvI.lookupAs, subst_lookup, raw_lookup in *.
          specialize (H u0).
          consider (FM.find u0 (env s)); try reflexivity.
          { intros. specialize (H0 _ eq_refl).
            destruct H0. destruct H0. rewrite H0 in *.
            destruct x0. simpl in *.
            consider (ExprD.exprD' u x e x0); intros; try congruence.
            inv_all; subst.
            generalize (@exprD'_lift ts _ _ u nil v x e x0); simpl.
            rewrite H1 in *.
            consider (ExprD.exprD' u (v ++ x) (lift 0 (length v) e) x0);
              intuition.
            match goal with
              | |- match match match ?X with _ => _ end with _ => _ end with _ => _ end =>
                consider X; intros
            end.
            inv_all. subst.
            rewrite H2. intros; eauto.
            specialize (H3 Hnil vs h). simpl in *. eauto.
            consider (ExprD.exprD' u (v ++ x) (lift 0 (length v) e) t); auto; intros.
            assert (WellTyped_expr (typeof_env u)
                                   (v ++ x) (lift 0 (length v) e) t).
            { rewrite ExprD.typeof_expr_exprD'. eauto. }
            assert (WellTyped_expr (typeof_env u)
                                   (v ++ x) (lift 0 (length v) e) x0).
            { rewrite ExprD.typeof_expr_exprD'. eauto. }
            red in H6; red in H7. rewrite H6 in H7. inv_all; subst.
            rewrite typ_cast_typ_refl in H4. congruence. }
          { autorewrite with exprD_rw.
            simpl; intros. unfold EnvI.lookupAs.
            destruct (nth_error u u0); auto.
            destruct s0.
            simpl in *.
            destruct (typ_cast_typ ts nil x0 t); auto. } }
      Qed.
*)
      Admitted.

      Theorem substD_lookup : forall (u v : EnvI.env (typD ts)) s uv e,
        lookup uv s = Some e ->
        subst_substD u v s ->
        exists val : sigT (typD ts nil),
          nth_error u uv = Some val /\
          exprD u v e (projT1 val) = Some (projT2 val).
      Proof.
        intros. eapply substD_sem in H0; eauto.
      Qed.

      Theorem WellTyped_lookup : forall (u v : tenv typ) s uv e t,
        subst_WellTyped u v s ->
        nth_error u uv = Some t ->
        lookup uv s = Some e ->
        ExprI.Safe_expr (Expr := @ExprD.Expr_expr ts _ _) u v e t.
      Proof.
        simpl in *.
        unfold subst_WellTyped, raw_WellTyped, subst_lookup, raw_lookup; intros.
        eapply FM.find_2 in H1. eapply H in H1.
        rewrite H0 in H1. destruct H1; intuition; inv_all; subst; auto.
      Qed.

      Lemma ex_iff : forall T (P Q : T -> Prop),
        (forall x, P x <-> Q x) -> ((exists x, P x) <-> (exists y, Q y)).
      Proof.
        intros. intuition.
        { destruct H0. exists x. eapply H; eauto. }
        { destruct H0. exists x. eapply H; eauto. }
      Qed.

      Lemma WellTyped_raw_subst_add : forall u s v uv e' t' e v' t,
        raw_WellTyped u v s ->
        nth_error u uv = Some t' ->
        WellTyped_expr u v e' t' ->
        (WellTyped_expr u (v' ++ v) (raw_subst (FM.add uv e' s) (length v') e) t <->
         WellTyped_expr u (v' ++ v) (raw_subst s (length v') e) t).
      Proof.
        induction e; simpl; intros;
        repeat (rewrite WellTyped_expr_App || rewrite WellTyped_expr_Abs ||
                        rewrite WellTyped_expr_Not || rewrite WellTyped_expr_Equal ||
                        rewrite WellTyped_expr_UVar ||
                        (eapply ex_iff; intros) ||
                        match goal with
                          | H : _ |- _ =>
                            rewrite H by eauto
                        end); try reflexivity.
        { change (t :: v' ++ v) with ((t :: v') ++ v).
          rewrite IHe by eauto. intuition. }
        { unfold raw_lookup.
          rewrite FACTS.add_o.
          consider (FM.E.eq_dec uv u0); try reflexivity.
          consider (FM.find u0 s).
          { intros.
            generalize (typeof_expr_lift _ u nil v' v e').
            generalize (typeof_expr_lift _ u nil v' v e0).
            unfold WellTyped_expr in *. simpl.
            intro X; rewrite X; clear X.
            intro X; rewrite X; clear X.
            red in e. subst. rewrite H1.
            eapply FM.find_2 in H2. eapply H in H2.
            destruct H2. destruct H2. rewrite H2 in *. inv_all; subst.
            unfold WellTyped_expr in *. rewrite H3. reflexivity. }
          { rewrite WellTyped_expr_UVar.
            generalize (typeof_expr_lift _ u nil v' v e'). simpl.
            unfold WellTyped_expr. red in e. subst.
            intro. rewrite H2. intuition; try congruence. } }
      Qed.

      Lemma WellTyped_raw_subst : forall u s v e v' t,
        raw_WellTyped u v s ->
        WellTyped_expr u (v' ++ v) e t ->
        WellTyped_expr u (v' ++ v) (raw_subst s (length v') e) t.
      Proof.
        clear. induction e; simpl; intros; auto.
        { eapply WellTyped_expr_App in H0.
          eapply WellTyped_expr_App.
          destruct H0; destruct H0. intuition.
          exists x. exists x0. intuition. }
        { eapply WellTyped_expr_Abs in H0.
          eapply WellTyped_expr_Abs.
          destruct H0. exists x. intuition subst.
          change (t :: v' ++ v) with ((t :: v') ++ v) in *.
          eapply IHe; eauto. }
        { unfold raw_lookup.
          consider (FM.find u0 s); intros; auto.
          red in H. eapply FM.find_2 in H1.
          specialize (H _ _ H1). destruct H.
          rewrite WellTyped_expr_UVar in H0.
          rewrite H0 in *. intuition; inv_all; subst; auto.
          unfold WellTyped_expr. generalize (@typeof_expr_lift _ _ _ u nil v' v e).
          simpl. intro X; rewrite X. eapply H3. }
      Qed.

      Lemma WellTyped_raw_subst_add_new : forall u s v uv e' t' e v',
        raw_lookup uv s = None ->
        nth_error u uv = Some t' ->
        WellTyped_expr u v e' t' ->
        (typeof_expr u (v' ++ v) (raw_subst (FM.add uv e' s) (length v') e) =
         typeof_expr u (v' ++ v) (raw_subst s (length v') e)).
      Proof.
        induction e; simpl; intros;
        repeat (rewrite WellTyped_expr_App || rewrite WellTyped_expr_Abs ||
                        rewrite WellTyped_expr_Not || rewrite WellTyped_expr_Equal ||
                        rewrite WellTyped_expr_UVar ||
                        (eapply ex_iff; intros) ||
                        match goal with
                          | H : _ |- _ =>
                            rewrite H by eauto
                        end); try reflexivity.
        { change (t :: v' ++ v) with ((t :: v') ++ v).
          rewrite IHe by eauto. intuition. }
        { unfold raw_lookup.
          rewrite FACTS.add_o.
          consider (FM.E.eq_dec uv u0); try reflexivity.
          red in e; subst.
          unfold raw_lookup in *.
          rewrite H. simpl.
          generalize (typeof_expr_lift _ u nil v' v e').
          unfold WellTyped_expr in *. simpl.
          intro X; rewrite X; clear X.
          rewrite H1. rewrite H0. reflexivity. }
      Qed.

      Theorem WellTyped_set : forall (uv : nat) (e : expr _) (s s' : subst) u v t,
        subst_WellTyped u v s ->
        nth_error u uv = Some t ->
        WellTyped_expr u v e t ->
        set uv e s = Some s' ->
        subst_WellTyped u v s'.
      Proof.
        simpl.
        unfold subst_set, subst_WellTyped. destruct s; simpl; intros.
        revert H2. gen_refl.
        generalize (@raw_set_WellFormed uv e env0). destruct s'; simpl.
        remember (raw_set uv e env0). destruct o; simpl in *; intros; try congruence.
        inv_all. inversion H2; clear H2; subst. clear w e0.
        red. intros.
        unfold raw_set in Heqo.
        consider (mentionsU uv (raw_subst env0 0 e)); try congruence.
        intros. inv_all; subst.
        eapply FACTS.map_mapsto_iff in H2.
        destruct H2; intuition subst.
        eapply FACTS.add_mapsto_iff in H5.
        intuition subst.
        { exists t. split; auto.
          clear wf1.
          generalize (@WellTyped_raw_subst_add u env0 v k
             (raw_subst env0 0 e) t (raw_subst env0 0 e) nil t H H0).
          simpl. intro. rewrite H2.
          rewrite raw_subst_idem by eauto.
          generalize (@WellTyped_raw_subst u env0 v e nil t H).
          simpl. intuition.
          generalize (@WellTyped_raw_subst u env0 v e nil t H).
          simpl. intuition. }
        { destruct (H _ _ H5).
          intuition. exists x0.
          split; auto.
          generalize (@WellTyped_raw_subst_add u env0 v uv
             (raw_subst env0 0 e) _ x nil x0 H H0).
          simpl. intros. rewrite H2.
          { generalize (@WellTyped_raw_subst u env0 v x nil x0 H).
            simpl. intuition. }
          { generalize (@WellTyped_raw_subst u env0 v e nil t H).
            simpl; intuition. } }
      Qed.

      Lemma raw_substD_raw_WellTyped : forall u v s,
        raw_substD u v s ->
        raw_WellTyped (typeof_env u) (typeof_env v) s.
      Proof.
        intros. rewrite raw_substD_sem in H.
        red. intros.
        apply FM.find_1 in H0.
        specialize (H _ _ H0).
        destruct H. intuition.
        rewrite nth_error_typeof_env. rewrite H1.
        eexists; split; eauto.
        eapply ExprD.typeof_expr_exprD.
        eauto.
      Qed.

      Lemma raw_substD_exprD' : forall u v s,
        raw_substD u v s ->
        forall e tv' t,
          let (tv,vs) := EnvI.split_env v in
          let (tu,us) := EnvI.split_env u in
          match exprD' tu (tv' ++ tv) (raw_subst s (length tv') e) t
              , exprD' tu (tv' ++ tv) e t
          with
            | Some l , Some r =>
              forall vs', l us (hlist_app vs' vs) = r us (hlist_app vs' vs)
            | None , None => True
            | _ , _ => False
          end.
      Proof.
(*
        induction e; simpl; intros; consider (split_env v);
        intros; autorewrite with exprD_rw.
        {(* change (
              let zzz t' (pf : Some t' = nth_error (tv' ++ x) v0)
                      (f : forall F : Type -> Type, F (typD ts nil t') -> F (typD ts nil t)) :=
                  (fun e : hlist (typD ts nil) (tv' ++ x) =>
                               match
                                 pf in (_ = t'')
                                 return
                                 (match t'' with
                                    | Some t0 => typD ts nil t0
                                    | None => unit
                                  end -> typD ts nil t)
                               with
                                 | eq_refl => fun x0 : typD ts nil t' => f (fun x => x) x0
                               end (hlist_nth e v0))
              in
              match
                match
                  nth_error (tv' ++ x) v0 as z
                  return
                  (z = nth_error (tv' ++ x) v0 ->
                   option (hlist (typD ts nil) (tv' ++ x) -> typD ts nil t))
                with
                  | Some t' =>
                    fun pf : Some t' = nth_error (tv' ++ x) v0 =>
                      match typ_cast_typ ts nil t' t with
                        | Some f =>
                          Some (zzz t' pf f)
                        | None => None
                      end
                  | None => fun _ : None = nth_error (tv' ++ x) v0 => None
                end eq_refl
              with
                | Some l =>
                  match
                    match
                      nth_error (tv' ++ x) v0 as z
                      return
                      (z = nth_error (tv' ++ x) v0 ->
                       option (hlist (typD ts nil) (tv' ++ x) -> typD ts nil t))
                    with
                      | Some t' =>
                        fun pf : Some t' = nth_error (tv' ++ x) v0 =>
                          match typ_cast_typ ts nil t' t with
                            | Some f =>
                              Some (zzz t' pf f)
                            | None => None
                          end
                      | None => fun _ : None = nth_error (tv' ++ x) v0 => None
                    end eq_refl
                  with
                    | Some r =>
                      forall vs' : hlist (typD ts nil) tv',
                        l (hlist_app vs' h) = r (hlist_app vs' h)
                    | None => False
                  end
                | None =>
                  match
                    match
                      nth_error (tv' ++ x) v0 as z
                      return
                      (z = nth_error (tv' ++ x) v0 ->
                       option (hlist (typD ts nil) (tv' ++ x) -> typD ts nil t))
                    with
                      | Some t' =>
                        fun pf : Some t' = nth_error (tv' ++ x) v0 =>
                          match typ_cast_typ ts nil t' t with
                            | Some f =>
                              Some (zzz t' pf f)
                            | None => None
                          end
                      | None => fun _ : None = nth_error (tv' ++ x) v0 => None
                    end eq_refl
                  with
                    | Some _ => False
                    | None => True
                  end
              end).
          intro zzz; clearbody zzz; revert zzz.
          gen_refl.
          destruct (nth_error (tv' ++ x) v0); auto; intros.
          simpl.
          match goal with
            | |- match match ?X with _ => _ end with None => match match ?Y with _ => _ end with _ => _ end | _ => _ end =>
              change Y with X ;
              consider X; try congruence
          end; auto. *) admit. }
        { repeat match goal with
                   | |- context [ match ?X with _ => _ end ] =>
                     (destruct X; try congruence); [ ]
                 end; auto. }
        { consider (split_env u); intros.
          assert (x0 = typeof_env u).
          { rewrite <- split_env_typeof_env. rewrite H1. reflexivity. }
          subst.
          specialize (raw_substD_raw_WellTyped H); intro.
          generalize (@raw_subst_typeof (typeof_env u) e1 x tv' s).
          autorewrite with exprD_rw.
          intro. rewrite H3.
          destruct (typeof_expr (typeof_env u) (tv' ++ x) e1); auto.
          destruct t0; auto.
          specialize (IHe1 tv' (tyArr t0_1 t0_2)).
          specialize (IHe2 tv' t0_1).
          repeat match goal with
                   | _ : context [ match ?X with _ => _ end ] |- _ =>
                     consider X; intros; try congruence
                   | |- context [ match ?X with _ => _ end ] =>
                     consider X; intros; try congruence
                 end; auto.
          { inv_all; subst. rewrite IHe1. f_equal. eauto. }
          assert (x = typeof_env v).
          { rewrite <- split_env_typeof_env. rewrite H0. reflexivity. }
          subst. auto. }
        { destruct t0; auto.
          specialize (IHe (t :: tv') t0_2). simpl in *.
          repeat match goal with
                   | _ : context [ match ?X with _ => _ end ] |- _ =>
                     consider X; intros; try congruence
                   | |- context [ match ?X with _ => _ end ] =>
                     consider X; intros; try congruence
                 end; auto.
          clear H2. inv_all; subst.
          eapply functional_extensionality. intros.
          specialize (IHe (Hcons x0 vs')). simpl in *; auto. }
        { rewrite raw_substD_sem in H.
          unfold ExprD.exprD in *.
          specialize (H u0).
          destruct (raw_lookup u0 s).
          { specialize (H _ eq_refl).
            destruct H. intuition.
            unfold lookupAs in *.
            rewrite H1. destruct x0; simpl in *.
            rewrite H0 in *.
            consider (ExprD.exprD' u x e x0); try congruence; intros.
            inv_all; subst.
            match goal with
              | |- match _ with Some _ => match match match ?X with _ => _ end
                                                with _ => _ end
                                          with _ => _ end
                             | _ => _ end =>
                consider X; intros
            end.
            { inv_all. subst.
              generalize (exprD'_lift _ u nil tv' x e t); simpl.
              rewrite H.
              destruct (ExprD.exprD' u (tv' ++ x) (lift 0 (length tv') e) t); auto.
              intros. specialize (H2 Hnil vs' h). simpl in *; auto. }
            { generalize (exprD'_lift _ u nil tv' x e t); simpl.
              consider (ExprD.exprD' u (tv' ++ x) (lift 0 (length tv') e) t); intuition.
              consider (ExprD.exprD' u x e t); intuition.
              clear H5.
              assert (WellTyped_expr (typeof_env u) x e t).
              { eapply ExprD.typeof_expr_exprD'; eauto. }
              assert (WellTyped_expr (typeof_env u) x e x0).
              { eapply ExprD.typeof_expr_exprD'; eauto. }
              red in H6; red in H5. rewrite H6 in H5. inv_all; subst.
              rewrite typ_cast_typ_refl in *. congruence. } }
          { autorewrite with exprD_rw.
            destruct (lookupAs u u0 t); auto. } }
      Qed. *)
      Admitted.

      Lemma raw_substD_exprD : forall u v s t e,
        raw_substD u v s ->
        exprD u v (raw_subst s 0 e) t =
        exprD u v e t.
      Proof.
        intros.
        generalize (raw_substD_exprD' H e nil t).
        unfold exprD. simpl.
        destruct (split_env v); intros.
        repeat match goal with
                   | _ : match ?X with _ => _ end |- _ =>
                     consider X; intros; try congruence
               end; intuition.
(*        specialize (H2 Hnil). simpl in *; f_equal; auto.
      Qed. *)
      Admitted.

(*
      Lemma raw_subst_exprD_add' : forall uv u v e' s x,
        raw_lookup uv s = None ->
        nth_error u uv = Some x ->
        exprD u v e' (projT1 x) = Some (projT2 x) ->
        forall e tv' t,
          let (tv,vs) := EnvI.split_env v in
          let (tu,us) := EnvI.split_env v in
          match exprD' u (tv' ++ tv) (raw_subst (FM.add uv e' s) (length tv') e) t
              , exprD' u (tv' ++ tv) (raw_subst s (length tv') e) t
          with
            | Some l , Some r =>
              forall vs', l (hlist_app vs' vs) = r (hlist_app vs' vs)
            | None , None => True
            | _ , _ => False
          end.
      Proof.
        induction e; simpl; auto; intros; autorewrite with exprD_rw.
        { destruct (split_env v).
          change (
              let zzz t' (pf : Some t' = nth_error (tv' ++ x0) v0)
                      (f : forall F : Type -> Type, F (typD ts nil t') -> F (typD ts nil t))  :=
                            (fun e : hlist (typD ts nil) (tv' ++ x0) =>
                               match
                                 pf in (_ = t'')
                                 return
                                 (match t'' with
                                    | Some t0 => typD ts nil t0
                                    | None => unit
                                  end -> typD ts nil t)
                               with
                                 | eq_refl => fun x1 : typD ts nil t' => f (fun x => x) x1
                               end (hlist_nth e v0))
              in
              match
                match
                  nth_error (tv' ++ x0) v0 as z
                  return
                  (z = nth_error (tv' ++ x0) v0 ->
                   option (hlist (typD ts nil) (tv' ++ x0) -> typD ts nil t))
                with
                  | Some t' =>
                    fun pf : Some t' = nth_error (tv' ++ x0) v0 =>
                      match typ_cast_typ ts nil t' t with
                        | Some f =>
                          Some (zzz t' pf f)
                        | None => None
                      end
                  | None => fun _ : None = nth_error (tv' ++ x0) v0 => None
                end eq_refl
              with
                | Some l =>
                  match
                    match
                      nth_error (tv' ++ x0) v0 as z
                      return
                      (z = nth_error (tv' ++ x0) v0 ->
                       option (hlist (typD ts nil) (tv' ++ x0) -> typD ts nil t))
                    with
                      | Some t' =>
                        fun pf : Some t' = nth_error (tv' ++ x0) v0 =>
                          match typ_cast_typ ts nil t' t with
                            | Some f =>
                              Some (zzz t' pf f)
                            | None => None
                          end
                      | None => fun _ : None = nth_error (tv' ++ x0) v0 => None
                    end eq_refl
                  with
                    | Some r =>
                      forall vs' : hlist (typD ts nil) tv',
                        l (hlist_app vs' h) = r (hlist_app vs' h)
                    | None => False
                  end
                | None =>
                  match
                    match
                      nth_error (tv' ++ x0) v0 as z
                      return
                      (z = nth_error (tv' ++ x0) v0 ->
                       option (hlist (typD ts nil) (tv' ++ x0) -> typD ts nil t))
                    with
                      | Some t' =>
                        fun pf : Some t' = nth_error (tv' ++ x0) v0 =>
                          match typ_cast_typ ts nil t' t with
                            | Some f =>
                              Some (zzz t' pf f)
                            | None => None
                          end
                      | None => fun _ : None = nth_error (tv' ++ x0) v0 => None
                    end eq_refl
                  with
                    | Some _ => False
                    | None => True
                  end
              end
            ).
          intro zzz; clearbody zzz; revert zzz.
          destruct (nth_error (tv' ++ x0) v0); auto.
          destruct (typ_cast_typ ts nil t0 t); auto. }
        { repeat match goal with
                   | |- context [ match ?X with _ => _ end ] =>
                     destruct X; intros
                 end; auto. }
        { consider (split_env v); intros.
          autorewrite with exprD_rw.
          erewrite WellTyped_raw_subst_add_new.
          2: eassumption.
          2: instantiate (1 := projT1 x); rewrite nth_error_typeof_env;
             rewrite H0; reflexivity.
          consider (typeof_expr (typeof_env u)
             (tv' ++ x0) (raw_subst s (length tv') e1)); intros; auto.
          destruct t0; auto.
          specialize (IHe2 tv' t0_1).
          specialize (IHe1 tv' (tyArr t0_1 t0_2)).
          repeat match goal with
                   | _ : context [ match ?X with _ => _ end ] |- _ =>
                     consider X; intros
                   | |- context [ match ?X with _ => _ end ] =>
                     consider X; intros
                 end; auto; try congruence.
          inv_all; subst. rewrite IHe1. rewrite IHe2. auto.
          eapply ExprD.lem_typeof_expr_exprD'.
          unfold exprD in *. rewrite H2 in *.
          destruct (exprD' u x0 e' (projT1 x)); try congruence. }
        { destruct (split_env v).
          autorewrite with exprD_rw.
          destruct t0; auto.
          specialize (IHe (t :: tv') t0_2).
          simpl in *.
          repeat match goal with
                   | |- match match ?X with _ => _ end with _ => _ end =>
                     consider X; auto; intros; try congruence
                 end.
          eapply functional_extensionality. intros.
          specialize (IHe (Hcons (F := typD ts nil) (p (fun x => x) x1) vs')).
          simpl in *. auto. }
        { unfold exprD in *.
          destruct (split_env v).
          unfold raw_lookup in *.
          rewrite FACTS.add_o.
          destruct (FM.E.eq_dec uv u0).
          { red in e. subst.
            rewrite H.
            autorewrite with exprD_rw.
            unfold lookupAs.
            rewrite H0. destruct x; simpl in *.
            generalize (exprD'_lift _ u nil tv' x0 e' t); simpl; intro.
            repeat match goal with
                       | _ : context [ match ?X with _ => _ end ] |- _ =>
                         (consider X; intros; try solve [ intuition | congruence ]); [ ]
                     end.
              match goal with
                | |- context [ typ_cast_typ ?A ?B ?C ?D ] =>
                  consider (typ_cast_typ A B C D)
              end; intros.
            { inv_all; subst. subst.
              repeat match goal with
                       | _ : context [ match ?X with _ => _ end ] |- _ =>
                         (consider X; intros; try solve [ intuition | congruence ]); [ ]
                     end.
              inv_all; subst. specialize (H4 Hnil vs' h).
              simpl in *. auto. }
            { repeat match goal with
                       | _ : context [ match ?X with _ => _ end ] |- _ =>
                         (consider X; intros; try solve [ intuition | congruence ]); [ ]
                     end.
              assert (exprD' u x0 e' t <> None) by congruence.
              assert (exprD' u x0 e' x <> None) by congruence.
              eapply ExprD.lem_typeof_expr_exprD' in H7.
              eapply ExprD.lem_typeof_expr_exprD' in H8.
              red in H7. red in H8.
              rewrite H7 in H8. inv_all; subst.
              rewrite typ_cast_typ_refl in H4. congruence. } }
          { match goal with
              | |- match ?x with _ => _ end =>
                destruct x
            end; auto. } }
      Qed.
*)

      Lemma raw_subst_exprD_add : forall uv u v e' s x e t,
        raw_lookup uv s = None ->
        nth_error u uv = Some x ->
        exprD u v e' (projT1 x) = Some (projT2 x) ->
        exprD u v (raw_subst (FM.add uv e' s) 0 e) t =
        exprD u v (raw_subst s 0 e) t.
      Proof.
(*
        intros.
        specialize (@raw_subst_exprD_add' uv u v e' s x H H0 H1 e nil t).
        simpl. unfold exprD.
        destruct (split_env v).
        destruct (exprD' u x0 (raw_subst (FM.add uv e' s) 0 e) t);
          destruct (exprD' u x0 (raw_subst s 0 e) t); intuition.
        specialize (H2 Hnil). simpl in *. rewrite H2; auto.
      Qed. *)
      Admitted.

      Lemma raw_substD_add : forall u v uv e s,
        raw_lookup uv s = None ->
        raw_substD u v (FM.add uv e s) ->
        raw_substD u v s /\
        exists x,
          nth_error u uv = Some x /\
          exprD u v e (projT1 x) = Some (projT2 x).
      Proof.
        intros.
        rewrite raw_substD_sem in *.
        unfold raw_lookup in *.
        intuition.
        specialize (H0 uv0 e0).
        rewrite FACTS.add_o in *.
        destruct (FM.E.eq_dec uv uv0).
        { red in e1; subst. congruence. }
        { destruct (H0 H1); intuition. }
      Qed.

      Lemma raw_substD_map : forall u v f s,
         (forall uv e x,
            raw_lookup uv s = Some e ->
            nth_error u uv = Some x ->
            exprD u v (f e) (projT1 x) = Some (projT2 x) ->
            exprD u v e (projT1 x) = Some (projT2 x)) ->
         raw_substD u v (FM.map f s) ->
         raw_substD u v s.
      Proof.
        intros.
        rewrite raw_substD_sem in *.
        intros. specialize (H0 uv (f e)).
        unfold raw_lookup in *.
        rewrite FACTS.map_o in H0. rewrite H1 in *.
        specialize (H0 eq_refl).
        destruct H0; intuition.
        rewrite H2.
        eexists; split; eauto.
      Qed.

      Theorem substD_set : forall (uv : nat) (e : expr _) (s s' : subst) u v,
        subst_substD u v s' ->
        lookup uv s = None ->
        set uv e s = Some s' ->
        subst_substD u v s /\
        (forall tv : sigT (typD ts nil),
           nth_error u uv = Some tv ->
           exprD u v e (projT1 tv) = Some (projT2 tv)).
      Proof.
        simpl. unfold subst_set, subst_lookup.
        intros. revert H1. destruct s; destruct s'; simpl in *.
        gen_refl. unfold subst_substD in *; simpl in *.
        generalize (@raw_set_WellFormed uv e env0).
        remember (raw_set uv e env0).
        destruct o; try congruence.
        intros; inv_all; subst.
        inversion H1; clear H1; subst. clear e0 w.
        unfold raw_set in *.
        consider (mentionsU uv (raw_subst env0 0 e)); try congruence.
        intros. inv_all; subst.
        eapply raw_substD_map in H.
        eapply raw_substD_add in H; eauto.
        { intuition.
          destruct H3. intuition.
          rewrite H in H4. inv_all; subst; auto.
          rewrite (@raw_substD_exprD _ _ _ (projT1 x) e H2) in H5.
          auto. }
        { intros. unfold raw_lookup in *.
          rewrite FACTS.add_o in *.
          destruct (FM.E.eq_dec uv uv0).
          { inv_all; subst.
            rewrite raw_subst_add_not_mentions in H4 by eauto.
            rewrite raw_subst_idem in *; eauto. }
          { rewrite raw_substD_sem in H.
            specialize (H uv).
            unfold raw_lookup in *.
            rewrite FACTS.map_o in H. rewrite FACTS.add_o in H.
            destruct (FM.E.eq_dec uv uv).
            2: red in n0; congruence.
            specialize (H _ eq_refl).
            destruct H; intuition; inv_all; subst.
            etransitivity; [ | eassumption ].
            rewrite (@raw_subst_exprD_add uv u v (raw_subst env0 0 e) env0 x0 e0 (projT1 x) H0 H5).
            rewrite raw_subst_normalized by eauto. reflexivity.
            rewrite raw_subst_add_not_mentions in * by eauto.
            rewrite raw_subst_idem in * by eauto. auto. } }
      Qed.

      Theorem substD_empty : forall u v,
        subst_substD u v subst_empty.
      Proof.
        red. red. simpl. intros. rewrite FM.fold_1.
        rewrite PROPS.elements_empty. simpl. exact I.
      Qed.

      Theorem WellTyped_empty : forall u v,
        subst_WellTyped u v subst_empty.
      Proof.
        red. red. simpl; intros.
        exfalso.
        eapply FACTS.empty_mapsto_iff in H. assumption.
      Qed.

      Instance SubstOk_subst : @SubstOk _ _ _ _ (@ExprD.Expr_expr ts _ _)  Subst_subst :=
      { substD := subst_substD
      ; WellTyped_subst := subst_WellTyped
      }.
      Proof.
        { eapply substD_empty. }
        { eapply WellTyped_empty. }
        { eauto using WellTyped_lookup. }
        { eapply substD_lookup. }
        { intros. eapply WellTyped_set; eauto. eapply H1. }
        { eapply substD_set. }
      Defined.

    End semantic.
  End hide_hints.
End Make.

Require FSets.FMapAVL.

Module UVar_ord <: OrderedType.OrderedType with Definition t := uvar
                                           with Definition eq := @eq uvar.
  Definition t := uvar.
  Definition eq := @eq uvar.
  Definition lt := @lt.

  Theorem eq_refl : forall x, eq x x.
  Proof. reflexivity. Qed.

  Theorem eq_sym : forall a b, eq a b -> eq b a.
  Proof. intros; symmetry; auto. Qed.

  Theorem eq_trans : forall a b c, eq a b -> eq b c -> eq a c.
  Proof. intros; etransitivity; eauto. Qed.

  Theorem lt_trans : forall a b c, lt a b -> lt b c -> lt a c.
  Proof. eapply Lt.lt_trans. Qed.

  Theorem lt_not_eq : forall a b, lt a b -> ~(eq a b).
  Proof. eapply NPeano.Nat.lt_neq. Qed.

  Definition compare (x y : t) : OrderedType.Compare lt eq x y :=
    match Compare_dec.nat_compare x y as r return
      Compare_dec.nat_compare x y = r -> OrderedType.Compare lt eq x y
      with
      | Lt => fun pf => OrderedType.LT (lt:=lt) (Compare_dec.nat_compare_Lt_lt _ _ pf)
      | Eq => fun pf => OrderedType.EQ (lt:=lt) (Compare_dec.nat_compare_eq _ _ pf)
      | Gt => fun pf => OrderedType.GT (lt:=lt) (Compare_dec.nat_compare_Gt_gt _ _ pf)
    end (refl_equal _).

  Definition eq_dec (x y : nat) : {x = y} + {x <> y} :=
    match EqNat.beq_nat x y as r return
      EqNat.beq_nat x y = r -> {x = y} + {x <> y} with
      | true => fun pf => left (EqNat.beq_nat_true _ _ pf)
      | false => fun pf => right (EqNat.beq_nat_false _ _ pf)
    end (refl_equal _).
End UVar_ord.

Module MAP := FMapAVL.Make UVar_ord.
Module SUBST := Make MAP.
