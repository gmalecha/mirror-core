Require Coq.FSets.FMapFacts.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Bool.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SubstI3.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.TypesI.

Set Implicit Arguments.
Set Strict Implicit.

(** Finite Maps **)
Require Import FMapInterface.

Let uvar : Type := nat.

Module Make (FM : WS with Definition E.t := uvar
                     with Definition E.eq := @eq uvar).

  Module FACTS := FMapFacts.WFacts FM.
  Module PROPS := FMapFacts.WProperties FM.

  Section exprs.
    Variable typ : Type.
    Context {RType_typ : RType typ}.
    Variable expr : Type.
    Variable Expr_expr : Expr _ expr.
    Variable ExprOk_expr : ExprOk Expr_expr.

    Variable mentionsU : uvar -> expr -> bool.

    Variable EqDec_eq_typ : EqDec typ (@eq typ).

    Definition raw : Type := FM.t expr.

    Definition normalized (this : raw) (e : expr) : Prop :=
      forall u, mentionsU u e = true -> ~FM.In u this.

    Definition WellFormed (this : raw) : Prop :=
      forall (k : uvar) e,
        FM.MapsTo k e this ->
        normalized this e.

    Definition raw_lookup : uvar -> raw -> option expr :=
       @FM.find _.

    Variable instantiate : (uvar -> option expr) -> nat -> expr -> expr.

    Definition raw_subst (s : raw) : nat -> expr -> expr :=
      instantiate (fun x => raw_lookup x s).

    Definition raw_set (u : uvar) (e : expr) (s : raw) : option raw :=
      let v' := raw_subst s 0 e in
      if mentionsU u v'
      then None
      else let s :=
               FM.add u v' (FM.map (instantiate (fun u' => if u ?[ eq ] u' then
                                                              Some v'
                                                           else None) 0) s)
           in Some s.


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

    Hypothesis instantiate_not_mentionsU
    : forall (f f' : uvar -> option expr) n e u',
        (forall u, u <> u' -> f u = f u) ->
        mentionsU u' e = false ->
        instantiate f n e = instantiate f' n e.

    Hypothesis instantiate_noop
    : forall (f : uvar -> option expr) e n,
        (forall u, mentionsU u e = true -> f u = None) ->
        instantiate f n e = e.

    Hypothesis instantiate_mentionsU
    : forall f n e u,
        mentionsU u (instantiate f n e) = true <->
        (   (f u = None /\ mentionsU u e = true)
         \/ exists u' e',
              f u' = Some e' /\
              mentionsU u' e = true/\
              mentionsU u e' = true).

    Hypothesis exprD'_strengthen_last
    : forall tus tvs e t val,
        mentionsU (length tus) e = false ->
        exprD' (tus ++ t :: nil) tvs e t = Some val ->
        exists val',
          exprD' tus tvs e t = Some val' /\
          forall us vs u,
            val (hlist_app us (Hcons u Hnil)) vs = val' us vs.

    (* normalized and instantiate *)
    Lemma wf_instantiate_normalized : forall s e n,
      WellFormed s ->
      normalized s (raw_subst s n e).
    Proof.
      unfold WellFormed, normalized, raw_subst. intros.
      eapply instantiate_mentionsU in H0.
      destruct H0.
      { destruct H0. unfold raw_lookup in H0.
        eapply FACTS.not_find_in_iff. assumption. }
      { forward_reason.
        eapply H. 2: eassumption.
        eapply FACTS.find_mapsto_iff. eapply H0. }
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
      unfold raw_subst. intros.
      eapply instantiate_not_mentionsU in H. eapply H.
      intros. simpl.
      unfold raw_lookup. rewrite FACTS.add_neq_o; auto.
    Qed.

    Definition raw_substD (tus tvs : list typ) (sub : raw)
    : option (hlist (typD nil) tus -> hlist (typD nil) tvs -> Prop) :=
      FM.fold (fun k v P =>
                 match nth_error_get_hlist_nth _ tus k with
                   | None => None
                   | Some (existT T get) =>
                     match exprD' tus tvs v T with
                       | Some val' =>
                         match P with
                           | None => None
                           | Some P =>
                             Some (fun us vs => get us = val' us vs /\ P us vs)
                         end
                       | None => None
                     end
                 end) sub (Some (fun _ _ => True)).

    Record subst : Type :=
    { env : raw
    ; wf : WellFormed env
    }.

    Definition subst_lookup (uv : uvar) (s : subst) : option expr :=
      raw_lookup uv s.(env).

    Definition subst_subst (s : subst) : nat -> expr -> expr :=
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

    Lemma raw_subst_normalized : forall r e n,
      normalized r e ->
      raw_subst r n e = e.
    Proof.
      unfold normalized, raw_subst. intros.
      eapply instantiate_noop.
      intros. eapply H in H0.
      unfold raw_lookup.
      eapply FACTS.not_find_in_iff. assumption.
    Qed.

    Lemma raw_subst_idem : forall e b c d,
      WellFormed c ->
      raw_subst c b (raw_subst c d e) = raw_subst c d e.
    Proof.
      intros.
      erewrite raw_subst_normalized; auto using wf_instantiate_normalized.
    Qed.

    Hypothesis instantiate_only_mentions
    : forall f g n e,
        (forall u, mentionsU u e = true -> f u = g u) ->
        instantiate f n e = instantiate g n e.


    Lemma mentionsU_subst : forall s u x n,
      mentionsU u (raw_subst s n x) = true <->
      (mentionsU u x = true /\ ~FM.In u s \/
       exists u' e',
         FM.MapsTo u' e' s /\
         mentionsU u' x = true /\
         mentionsU u e' = true).
    Proof.
      intros. unfold raw_subst. rewrite instantiate_mentionsU.
      unfold raw_lookup.
      rewrite <- FACTS.not_find_in_iff.
      intuition.
      { right. forward_reason. do 2 eexists.
        intuition eauto. }
      { right. forward_reason. do 2 eexists.
        intuition eauto.
        apply FACTS.find_mapsto_iff. assumption. }
    Qed.

    Lemma mentionsU_add_normalized : forall u e s x n,
      normalized s x ->
      raw_subst (FM.add u e s) n x =
      raw_subst (FM.add u e (FM.empty _)) n x.
    Proof.
      unfold normalized, raw_subst; intros.
      eapply instantiate_only_mentions.
      unfold raw_lookup. intros.
      repeat rewrite FACTS.add_o.
      destruct (FM.E.eq_dec u u0); auto.
      rewrite FACTS.empty_o.
      rewrite <- FACTS.not_find_in_iff; eauto.
    Qed.

    Ltac go :=
      repeat match goal with
               | H : exists x, _ |- _ =>
                 destruct H
             end.

    Theorem raw_set_WellFormed : forall u e s s',
      raw_set u e s = Some s' ->
      WellFormed s ->
      WellFormed s'.
    Proof.
      unfold raw_set; intros.
      consider (mentionsU u (raw_subst s 0 e)); try congruence; intros.
      inv_all; subst.
      red in H0. red. intros.
      rewrite FACTS.add_mapsto_iff in H1.
      destruct H1.
      { destruct H1; subst.
        red. intros. intro.
        eapply FACTS.add_in_iff in H2.
        destruct H2.
        + subst. congruence.
        + eapply FM.map_2 in H2.
          eapply mentionsU_subst in H1.
          destruct H1.
          - intuition.
          - forward_reason. eapply H0 in H1. red in H1.
            eapply H1 in H4. eauto. }
      { forward_reason.
        eapply FACTS.map_mapsto_iff in H2.
        forward_reason. subst.
        red; intros.
        intro. eapply FACTS.add_in_iff in H4.
        destruct H4.
        + subst. eapply instantiate_mentionsU in H2.
          destruct H2.
          - forward.
          - forward_reason. forward.
        + rewrite FACTS.map_in_iff in H4.
          eapply instantiate_mentionsU in H2.
          destruct H2; forward_reason; forward.
          - eapply H0 in H3. red in H3. eapply H3 in H5; eauto.
          - inv_all. subst.
            eapply instantiate_mentionsU in H6.
            destruct H6; forward_reason.
            * unfold raw_lookup in H2.
              apply FACTS.not_find_in_iff in H2. auto.
            * unfold raw_lookup in H2.
              eapply FM.find_2 in H2.
              eapply H0 in H2. red in H2.
              eapply H2 in H7. auto. }
    Qed.

    Lemma wf_empty : WellFormed (FM.empty expr).
    Proof.
      red. red. intros.
      intro.
      apply FACTS.empty_in_iff in H1. auto.
    Qed.

    Definition subst_empty : subst :=
    {| env := FM.empty _ ; wf := wf_empty |}.

    Instance Subst_subst : Subst raw expr :=
    { lookup := raw_lookup
    ; domain := fun x => List.map (@fst _ _) (FM.elements x)
    }.

    Fixpoint raw_pull (from count : nat) (sub : raw) : option raw :=
      match count with
        | 0 => Some sub
        | S count' =>
          match FM.find (from + count') sub with
            | None => None
            | Some _ => raw_pull from count' (FM.remove (from + count') sub)
          end
      end.

(** TODO: This is slightly more efficient, but harder to work with
    Fixpoint raw_pull (from count : nat) (sub : raw) {struct count}
    : option raw :=
      match count with
        | 0 => Some sub
        | S count =>
          match FM.find from sub with
            | None => None
            | Some _ => raw_pull (S from) count (FM.remove from sub)
          end
      end.
**)

    Instance SubstUpdate_subst : SubstUpdate raw expr :=
    { set := raw_set
    ; pull := raw_pull
    ; empty := FM.empty _
    }.

    Lemma None_becomes_None
    : forall tus tvs l, fold_left
         (fun
            (a0 : option
                    (hlist (typD nil) tus -> hlist (typD nil) tvs -> Prop))
            (p : FM.key * expr) =>
          match nth_error_get_hlist_nth (typD nil) tus (fst p) with
          | Some (existT T get) =>
              match exprD' tus tvs (snd p) T with
              | Some val' =>
                  match a0 with
                  | Some P1 =>
                      Some
                        (fun (us : hlist (typD nil) tus)
                           (vs : hlist (typD nil) tvs) =>
                         get us = val' us vs /\ P1 us vs)
                  | None => None
                  end
              | None => None
              end
          | None => None
          end) l None = None.
    Proof.
      clear. induction l; simpl; auto.
      forward.
    Qed.

    Lemma substD_weaken
    : forall (tus tvs : tenv typ) (tus' tvs' : list typ) (s : raw)
             (sD : hlist (typD nil) tus -> hlist (typD nil) tvs -> Prop),
        raw_substD tus tvs s = Some sD ->
        exists
          sD' : hlist (typD nil) (tus ++ tus') ->
                hlist (typD nil) (tvs ++ tvs') -> Prop,
          raw_substD (tus ++ tus') (tvs ++ tvs') s = Some sD' /\
          (forall (us : hlist (typD nil) tus) (us' : hlist (typD nil) tus')
                  (vs : hlist (typD nil) tvs) (vs' : hlist (typD nil) tvs'),
             sD us vs <-> sD' (hlist_app us us') (hlist_app vs vs')).
    Proof.
      intros.
      unfold raw_substD in *.
      rewrite FM.fold_1 in *.
      revert H.
      match goal with
        | |- fold_left _ _ (Some ?X) = _ -> ?G =>
          match G with
            | context [ fold_left _ _ (Some ?Y) ] =>
              remember X ; remember Y (*;
              assert (forall us vs us' vs',
                X us vs <-> Y (hlist_app us us') (hlist_app vs vs')) by reflexivity ;
              generalize dependent X ; generalize dependent Y
 *)
          end
      end.
      assert (forall us vs us' vs',
                P us vs <-> P0 (hlist_app us us') (hlist_app vs vs')).
      { subst. reflexivity. }
      clear HeqP HeqP0.
      generalize dependent P; revert P0; revert sD.
      induction (FM.elements s); simpl.
      { intros. inv_all; subst.
        eexists; split; eauto. }
      { intros.
        match goal with
          | H : fold_left _ _ ?X = Some _ |- _ =>
            consider X; intros ; try solve [ rewrite None_becomes_None in *; congruence ]
        end.
        forward. inv_all; subst.

        eapply nth_error_get_hlist_nth_weaken with (ls' := tus') in H2.
        simpl in *.
        eapply exprD'_weaken with (tus' := tus') (tvs' := tvs') in H3; eauto with typeclass_instances.
        forward_reason.
        Cases.rewrite_all_goal.
        eapply IHl in H1; eauto with typeclass_instances.
        clear H1. intros. simpl.
        erewrite H; clear H. erewrite H3; clear H3.
        erewrite H4; clear H4. reflexivity. }
    Qed.

    Definition sem_preserves_if ts tus tvs
               (P : hlist _ tus -> hlist _ tvs -> Prop)
               (R : forall t, relation (typD ts t))
               (f : uvar -> option expr) : Prop :=
      forall u e t get,
        f u = Some e ->
        nth_error_get_hlist_nth _ tus u = Some (@existT _ _ t get) ->
        exists eD,
          exprD' tus tvs e t = Some eD /\
          forall us vs,
            P us vs ->
            get us = eD us vs.

    Hypothesis exprD'_instantiate
    : forall tus tvs f e tvs' t eD P,
        @sem_preserves_if nil tus tvs P (fun t => @eq _) f ->
        exprD' tus (tvs' ++ tvs) e t = Some eD ->
        exists eD',
          exprD' tus (tvs' ++ tvs) (instantiate f (length tvs') e) t = Some eD' /\
          forall us vs vs',
            P us vs ->
            eD us (hlist_app vs' vs) = eD' us (hlist_app vs' vs).

    Definition eq_option_A tus tvs
        (x y : option (hlist (typD nil) tus -> hlist (typD nil) tvs -> Prop))
    : Prop :=
           match x with
             | Some x0 =>
               match y with
                 | Some y0 =>
                   forall (a : hlist (typD nil) tus) (b : hlist (typD nil) tvs),
                     x0 a b <-> y0 a b
                 | None => False
               end
             | None => match y with
                         | Some _ => False
                         | None => True
                       end
           end.

    Theorem Proper_substD
    : forall tus tvs,
        Proper (eq ==> eq ==> @eq_option_A tus tvs ==> @eq_option_A tus tvs)
               (fun (k : FM.key) (v : expr)
                    (P : option (hlist (typD nil) tus -> hlist (typD nil) tvs -> Prop)) =>
                  match nth_error_get_hlist_nth (typD nil) tus k with
                    | Some (existT T get) =>
                      match exprD' tus tvs v T with
                        | Some val' =>
                          match P with
                            | Some P0 =>
                              Some
                                (fun (us : hlist (typD nil) tus)
                                     (vs : hlist (typD nil) tvs) =>
                                   get us = val' us vs /\ P0 us vs)
                            | None => None
                          end
                        | None => None
                      end
                    | None => None
                  end).
    Proof.
      unfold eq_option_A.
      do 4 red; intros.
      destruct x1; destruct y1; try solve [ intuition ].
      { subst. forward. intuition; eapply H1; auto. }
      { subst. forward. }
    Qed.

    Lemma Transpose_substD
    : forall tus tvs,
        PROPS.transpose_neqkey
          (@eq_option_A tus tvs)
          (fun (k : FM.key) (v : expr)
               (P : option (hlist (typD nil) tus -> hlist (typD nil) tvs -> Prop)) =>
             match nth_error_get_hlist_nth (typD nil) tus k with
               | Some (existT T get) =>
                 match exprD' tus tvs v T with
                   | Some val' =>
                     match P with
                       | Some P0 =>
                         Some
                           (fun (us : hlist (typD nil) tus)
                                (vs : hlist (typD nil) tvs) =>
                              get us = val' us vs /\ P0 us vs)
                       | None => None
                     end
                   | None => None
                 end
               | None => None
             end).
    Proof.
      unfold eq_option_A.
      red; intros.
      repeat match goal with
               | |- context [ match ?X with _ => _ end ] =>
                 match X with
                   | match _ with _ => _ end => fail 1
                   | _ => destruct X; auto
                 end
             end.
      intros. intuition.
    Qed.

    Local Instance Equivalence_substD tus tvs
    : Equivalence (@eq_option_A tus tvs).
    Proof.
      unfold eq_option_A.
      clear. constructor; red; intros.
      { destruct x; intuition. }
      { destruct x; destruct y; intuition; eapply H; eauto. }
      { destruct x; destruct y; destruct z; eauto; intros.
        rewrite H. eauto.
        intuition. }
    Qed.

    Lemma substD_lookup'
    : forall (s : raw) (uv : nat) (e : expr),
        lookup uv s = Some e ->
        forall (tus tvs : tenv typ)
               (sD : hlist (typD nil) tus -> hlist (typD nil) tvs -> Prop),
          raw_substD tus tvs s = Some sD ->
          exists
            (t : typ) (val : hlist (typD nil) tus ->
                             hlist (typD nil) tvs -> typD nil t)
            (pf : Some t = nth_error tus uv),
            exprD' tus tvs e t = Some val /\
            (forall (us : hlist (typD nil) tus) (vs : hlist (typD nil) tvs),
               sD us vs ->
               hlist_nth us uv =
               match
                 pf in (_ = t0)
                 return match t0 with
                          | Some x => typD nil x
                          | None => unit
                        end
               with
                 | eq_refl => val us vs
               end).
    Proof.
      intros.
      unfold raw_substD in *.
      match goal with
        | H : FM.fold _ _ (Some ?X) = _ |- _ =>
          generalize dependent X
      end.
      revert sD.
      generalize dependent s. intro s.
      eapply PROPS.map_induction with (m := s).
      { simpl; intros.
        exfalso. clear - H0 H.
        unfold raw_lookup in H0.
        red in H.
        eapply FM.find_2 in H0.
        eapply H. eauto. }
      { intros.
        generalize H1.
        match goal with
          | H : FM.fold ?F _ ?R = _ |- _ =>
            eapply PROPS.fold_Add
            with (eqA := @eq_option_A tus tvs) (f := F) (i := R) in H1;
              eauto using Equivalence_substD, Transpose_substD, Proper_substD
        end; eauto.
        { simpl in H2. unfold raw_lookup in H2.
          intro. red in H4.
          rewrite H4 in *; clear H4.
          erewrite FACTS.add_o in H2.
          consider (FM.E.eq_dec x uv).
          { red in e1. intros; inv_all; subst.
            change_rewrite H3 in H1.
            red in H1.
            progress forward.
            inv_all; subst.
            eapply nth_error_get_hlist_nth_Some in H4; simpl in *;
            forward_reason.
            do 3 eexists; split; eauto.
            instantiate (1 := eq_sym x0).
            intros. eapply H2 in H4; clear H2.
            destruct H4.
            rewrite <- H2. rewrite H1. clear.
            destruct x0. reflexivity. }
          { intro.
            change_rewrite H3 in H1.
            red in H1.
            forward; inv_all; subst.
            specialize (H H2 _ _ H7); clear H2 H7.
            forward_reason.
            do 3 eexists; split; eauto.
            intros. eapply H1.
            apply H4 in H2; intuition. } } }
    Qed.

    Lemma substD_lookup
    : forall (s : raw) (uv : nat) (e : expr),
        WellFormed s ->
        lookup uv s = Some e ->
        forall (tus tvs : tenv typ)
               (sD : hlist (typD nil) tus -> hlist (typD nil) tvs -> Prop),
          raw_substD tus tvs s = Some sD ->
          exists
            (t : typ) (val : hlist (typD nil) tus ->
                             hlist (typD nil) tvs -> typD nil t)
            (pf : Some t = nth_error tus uv),
            exprD' tus tvs e t = Some val /\
            (forall (us : hlist (typD nil) tus) (vs : hlist (typD nil) tvs),
               sD us vs ->
               hlist_nth us uv =
               match
                 pf in (_ = t0)
                 return match t0 with
                          | Some x => typD nil x
                          | None => unit
                        end
               with
                 | eq_refl => val us vs
               end).
    Proof.
      intros; eapply substD_lookup'; eauto.
    Qed.

    Lemma sem_preserves_if_raw_substD
    : forall ts tus tvs s sD,
        raw_substD tus tvs s = Some sD ->
        @sem_preserves_if ts tus tvs sD (fun _ => @eq _)
                          (fun u => raw_lookup u s).
    Proof.
      clear - EqDec_eq_typ. intros.
      red. intros.
      eapply substD_lookup' in H0; eauto.
      eapply nth_error_get_hlist_nth_Some in H1.
      forward_reason. simpl in *.
      assert (x = t) by congruence.
      subst.
      eexists; split; eauto. intros.
      rewrite H1.
      specialize (H2 us vs H3). clear H3.
      simpl in *.
      change_rewrite H2.
      clear - EqDec_eq_typ.
      destruct x1. rewrite (UIP_refl x2). reflexivity.
    Qed.

    Lemma WellFormed_domain
    : forall (s : raw) (ls : list nat),
        WellFormed s ->
        map fst (FM.elements s) = ls ->
        forall n : nat, In n ls <-> raw_lookup n s <> None.
    Proof.
      clear. intros.
      subst. rewrite in_map_iff.
      unfold raw_lookup. split; intros.
      { destruct H0. intuition; subst.
        eapply FACTS.not_find_in_iff in H1. apply H1.
        red. exists (snd x).
        eapply FM.elements_2. clear - H3.
        induction (FM.elements s).
        { inversion H3. }
        { inversion H3. subst. left. destruct x; simpl. compute. auto.
          right. auto. } }
      { consider (FM.find n s); intros; try congruence.
        eapply FM.find_2 in H0.
        exists (n,e). split; auto.
        eapply FM.elements_1 in H0.
        clear - H0.
        induction H0.
        { inversion H. red in H0. simpl in *. subst. destruct y; auto. }
        { right; auto. } }
    Qed.

    Instance SubstOk_subst : SubstOk Expr_expr Subst_subst :=
    {| WellFormed_subst := WellFormed
     ; substD := raw_substD
     ; substD_weaken := substD_weaken
     ; substD_lookup := substD_lookup
     ; WellFormed_domain := WellFormed_domain
     |}.

    Lemma WellFormed_empty : WellFormed_subst (FM.empty expr).
    Proof.
      compute. intros.
      eapply FACTS.empty_mapsto_iff. eauto.
    Qed.

    Lemma substD_empty
    : forall tus tvs : tenv typ,
      exists P : hlist (typD nil) tus -> hlist (typD nil) tvs -> Prop,
        substD tus tvs (empty (expr:=expr)) = Some P /\
        (forall (us : hlist (typD nil) tus) (vs : hlist (typD nil) tvs),
           P us vs).
    Proof.
      clear. simpl; intros.
      unfold raw_substD.
      rewrite FM.fold_1.
      cutrewrite (FM.elements (FM.empty expr) = nil).
      { simpl. eexists; split; eauto. simpl. auto. }
      { apply PROPS.elements_Empty.
        eapply FM.empty_1. }
    Qed.

    Lemma Empty_map
    : forall T U (m : FM.t T) (f : T -> U),
        FM.Empty m -> FM.Empty (FM.map f m).
    Proof.
      clear.
      unfold FM.Empty. intros.
      rewrite FACTS.map_mapsto_iff.
      intro. destruct H0 as [ ? [ ? ? ] ].
      eapply H; eauto.
    Qed.

    Lemma map_Add
    : forall T U (m m' : FM.t T) (f : T -> U) k e,
        PROPS.Add k e m m' ->
        FM.Equal (FM.map f m') (FM.add k (f e) (FM.map f m)).
    Proof.
      clear. intros.
      red. intros. red in H.
      rewrite FACTS.map_o. rewrite H.
      do 2 rewrite FACTS.add_o.
      rewrite FACTS.map_o.
      destruct (FM.E.eq_dec k y); auto.
    Qed.

    Lemma map_fold
    : forall (elt' elt A : Type) (eqA : A -> A -> Prop),
        Equivalence eqA ->
        forall (f : FM.key -> elt -> A -> A) (g : elt' -> elt),
          Proper (eq ==> eq ==> eqA ==> eqA) f ->
          PROPS.transpose_neqkey eqA f ->
          forall (m : FM.t elt') (i : A),
            eqA (FM.fold f (FM.map g m) i)
                (FM.fold (fun i e a => f i (g e) a) m i).
    Proof.
      clear. do 9 intro.
      intros m i.
      eapply PROPS.fold_rec with (m := m).
      { intros.
        eapply PROPS.fold_Empty; eauto.
        eapply Empty_map. auto. }
      { intros.
        etransitivity. eapply PROPS.fold_Equal; eauto.
        eapply map_Add. eassumption.
        etransitivity. eapply PROPS.fold_add with (eqA := eqA); eauto.
        { rewrite FACTS.map_in_iff. assumption. }
        { rewrite H0; try reflexivity.
          eapply H5; clear H5. } }
    Qed.

    Inductive Roption {T} (R : T -> T -> Prop) : option T -> option T -> Prop :=
    | Roption_None : Roption R None None
    | Roption_Some : forall a b, R a b -> Roption R (Some a) (Some b).

    Instance Equivalence_Roption A (R : A -> _) : Equivalence R -> Equivalence (Roption R).
    Proof.
      clear.
      intros.
      constructor; red; intros.
      { destruct x; first [ apply Roption_None | apply Roption_Some ].
        reflexivity. }
      { inversion H0. apply Roption_None. subst.
        constructor. symmetry. assumption. }
      { destruct H0. inversion H1. constructor.
        inversion H1. subst. constructor. etransitivity; eauto. }
    Qed.

    Lemma raw_substD_self_instantiate
    : forall tus tvs s sD (*Hwf : WellFormed s*),
        raw_substD tus tvs s = Some sD ->
        exists sD',
          raw_substD tus tvs (FM.map (raw_subst s 0) s) = Some sD' /\
          forall us vs,
            sD us vs -> sD' us vs.
    Proof.
      intros. generalize H.
      rename H into H_holdback.
      unfold raw_substD. intros.
      cut (exists sD' : hlist (typD nil) tus -> hlist (typD nil) tvs -> Prop,
             FM.fold
               (fun (k : FM.key) (v : expr)
                    (P : option (hlist (typD nil) tus -> hlist (typD nil) tvs -> Prop)) =>
                  let v := raw_subst s 0 v in
                  match nth_error_get_hlist_nth (typD nil) tus k with
                    | Some (existT T get) =>
                      match exprD' tus tvs v T with
                        | Some val' =>
                          match P with
                            | Some P0 =>
                              Some
                                (fun (us : hlist (typD nil) tus)
                                     (vs : hlist (typD nil) tvs) =>
                                   get us = val' us vs /\ P0 us vs)
                            | None => None
                          end
                        | None => None
                      end
                    | None => None
                  end) s
               (Some
                  (fun (_ : hlist (typD nil) tus) (_ : hlist (typD nil) tvs) => True)) =
             Some sD' /\
             (forall (us : hlist (typD nil) tus) (vs : hlist (typD nil) tvs),
                sD us vs -> sD' us vs)).
      { intros.
        forward_reason.
        match goal with
          | |- exists x, FM.fold ?F ?S ?A = _ /\ _ =>
            generalize (@map_fold expr expr _ (@eq_option_A tus tvs) _ F (raw_subst s 0)
                                  (@Proper_substD _ _) (@Transpose_substD _ _) s A)
        end.
        intro XXX.
        red in XXX.
        change_rewrite H0 in XXX.
        forward.
        change_rewrite H2.
        eexists; split; eauto.
        intros. eapply XXX. eapply H1. assumption. }
      { revert H.
        cut (FM.fold
                 (fun (k : FM.key) (v : expr)
                      (P : option (hlist (typD nil) tus -> hlist (typD nil) tvs -> Prop)) =>
                    match nth_error_get_hlist_nth (typD nil) tus k with
                      | Some (existT T get) =>
                        match exprD' tus tvs v T with
                          | Some val' =>
                            match P with
                              | Some P0 =>
                                Some
                                  (fun (us : hlist (typD nil) tus)
                                       (vs : hlist (typD nil) tvs) =>
                                     get us = val' us vs /\ P0 us vs)
                              | None => None
                            end
                          | None => None
                        end
                      | None => None
                    end) s
                 (Some
                    (fun (_ : hlist (typD nil) tus) (_ : hlist (typD nil) tvs) => True)) =
               Some sD ->
               exists sD' : hlist (typD nil) tus -> hlist (typD nil) tvs -> Prop,
                 FM.fold
                   (fun (k : FM.key) (v : expr)
                        (P : option (hlist (typD nil) tus -> hlist (typD nil) tvs -> Prop)) =>
                      let v0 := raw_subst s 0 v in
                      match nth_error_get_hlist_nth (typD nil) tus k with
                        | Some (existT T get) =>
                          match exprD' tus tvs v0 T with
                            | Some val' =>
                              match P with
                                | Some P0 =>
                                  Some
                                    (fun (us : hlist (typD nil) tus)
                                         (vs : hlist (typD nil) tvs) =>
                                       get us = val' us vs /\ P0 us vs)
                                | None => None
                              end
                            | None => None
                          end
                        | None => None
                      end) s
                   (Some
                      (fun (_ : hlist (typD nil) tus) (_ : hlist (typD nil) tvs) => True)) =
                 Some sD' /\
                 (forall (us : hlist (typD nil) tus) (vs : hlist (typD nil) tvs),
                    sD us vs ->
                    sD us vs -> sD' us vs)).
        { intros. eapply H in H0.
          forward_reason. eexists; split; eauto.
          intros. eauto. }
        { generalize sD at 1 3.
        match goal with
          | |- forall x, FM.fold ?F _ ?X = _ ->
                         exists y, FM.fold ?G _ ?Y = _ /\ _ =>
            cut (@eq_option_A tus tvs X Y) ;
            [ generalize X ; generalize Y ;
              do 3 intro ; eapply PROPS.fold_rel with (m := s) (f := F) (g := G)
            | ]
        end.
        { intros. subst.
          red in H. forward. subst.
          eexists; split; eauto.
          intros. apply H0. assumption. }
        { intros. forward.
          subst. inv_all; subst.
          specialize (H5 _ eq_refl).
          forward_reason. subst.
          change_rewrite H3.
          simpl.
          eapply exprD'_instantiate with (tvs' := nil) (tvs := tvs) (f := fun x => raw_lookup x s) (P := sD) in H4.
          simpl in *.
          unfold raw_subst. forward_reason.
          rewrite H1. eexists; split; eauto.
          intros. split; eauto.
          { forward_reason. rewrite H6.
            specialize (H4 us vs Hnil); simpl in *. eauto. }
          { forward_reason; eauto. }
          { eapply sem_preserves_if_raw_substD; eauto. } }
        { simpl. reflexivity. } } }
    Qed.

    Lemma raw_substD_instantiate'
    : forall tus tvs s sD f P,
        @sem_preserves_if nil tus tvs P (fun t => @eq _) f ->
        raw_substD tus tvs s = Some sD ->
        exists sD',
          raw_substD tus tvs (FM.map (instantiate f 0) s) = Some sD' /\
          forall us vs,
            P us vs ->
            (sD' us vs <-> sD us vs).
    Proof.
      unfold raw_substD. intros.
      cut (exists sD' : hlist (typD nil) tus -> hlist (typD nil) tvs -> Prop,
             FM.fold
               (fun (k : FM.key) (v : expr)
                    (P : option (hlist (typD nil) tus -> hlist (typD nil) tvs -> Prop)) =>
                  let v := instantiate f 0 v in
                  match nth_error_get_hlist_nth (typD nil) tus k with
                    | Some (existT T get) =>
                      match exprD' tus tvs v T with
                        | Some val' =>
                          match P with
                            | Some P0 =>
                              Some
                                (fun (us : hlist (typD nil) tus)
                                     (vs : hlist (typD nil) tvs) =>
                                   get us = val' us vs /\ P0 us vs)
                            | None => None
                          end
                        | None => None
                      end
                    | None => None
                  end) s
               (Some
                  (fun (_ : hlist (typD nil) tus) (_ : hlist (typD nil) tvs) => True)) =
             Some sD' /\
             (forall (us : hlist (typD nil) tus) (vs : hlist (typD nil) tvs),
                P us vs ->
                (sD' us vs <-> sD us vs))).
      { intros.
        forward_reason.
        match goal with
          | |- exists x, FM.fold ?F ?S ?A = _ /\ _ =>
            generalize (@map_fold expr expr _ (@eq_option_A tus tvs) _ F (instantiate f 0)
                                  (@Proper_substD _ _) (@Transpose_substD _ _) s A)
        end.
        intro XXX.
        red in XXX.
        change_rewrite H1 in XXX.
        forward.
        eexists; split; eauto.
        intros. etransitivity; eauto. }
      { revert H0. revert sD.
        match goal with
          | |- forall x, FM.fold ?F _ ?X = _ ->
               exists y, FM.fold ?G _ ?Y = _ /\ _ =>
            eapply PROPS.fold_rel with (m := s) (f := F) (g := G)
        end.
        { intros. inv_all; subst.
          eexists; split; eauto.
          simpl. reflexivity. }
        { intros.
          forward. inv_all; subst.
          specialize (H5 _ eq_refl).
          forward_reason. subst.
          change_rewrite H3.
          eapply exprD'_instantiate with (tvs' := nil) in H4; eauto.
          forward_reason. simpl in *.
          change_rewrite H1.
          eexists; split; [ reflexivity | ].
          simpl. intros. rewrite H2 by eauto.
          specialize (H4 us vs Hnil H5).
          simpl in *. rewrite H4. reflexivity. } }
    Qed.

    Lemma raw_substD_add
    : forall tus tvs uv e t s sD eD get,
        raw_lookup uv s = None ->
        nth_error_get_hlist_nth _ tus uv = Some (@existT _ _ t get) ->
        exprD' tus tvs e t = Some eD ->
        raw_substD tus tvs s = Some sD ->
        exists sD',
          raw_substD tus tvs (FM.add uv e s) = Some sD' /\
          forall us vs,
            sD' us vs <->
            (sD us vs /\ get us = eD us vs).
    Proof.
      intros.
      unfold raw_substD.
      assert (~ FM.In uv s).
      { clear - H. unfold raw_lookup in H.
        eapply FACTS.not_find_in_iff. assumption. }
      match goal with
        | |- exists x , FM.fold ?F (FM.add ?U ?E ?M) ?X = _ /\ _ =>
          generalize (@PROPS.fold_add _ _ (@eq_option_A tus tvs) _ F
                                      (@Proper_substD tus tvs)
                                      (@Transpose_substD tus tvs) M U E X H3)
      end.
      intro XXX.
      change_rewrite H0 in XXX.
      change_rewrite H1 in XXX.
      change_rewrite H2 in XXX.
      unfold eq_option_A in XXX.
      forward.
      eexists; split. eapply H4.
      intros. rewrite XXX; clear XXX.
      clear. split; intuition.
    Qed.

    Lemma substD_set
    : forall (uv : nat) (e : expr) (s s' : raw),
        set uv e s = Some s' ->
        lookup uv s = None ->
        WellFormed_subst s ->
        WellFormed_subst s' /\
        (forall (tus tvs : tenv typ) (t : typ)
                (val : hlist (typD nil) tus -> hlist (typD nil) tvs -> typD nil t)
                (sD : hlist (typD nil) tus -> hlist (typD nil) tvs -> Prop),
           substD tus tvs s = Some sD ->
           forall pf : Some t = nth_error tus uv,
             exprD' tus tvs e t = Some val ->
             exists sD' : hlist (typD nil) tus -> hlist (typD nil) tvs -> Prop,
               substD tus tvs s' = Some sD' /\
               (forall (us : hlist (typD nil) tus) (vs : hlist (typD nil) tvs),
                  sD' us vs ->
                  sD us vs /\
                  hlist_nth us uv =
                  match
                    pf in (_ = t0)
                    return match t0 with
                             | Some x => typD nil x
                             | None => unit
                           end
                  with
                    | eq_refl => val us vs
                  end)).
    Proof.
      unfold set; simpl; intros. unfold raw_set in *.
      forward. inv_all; subst.
      split.
      { generalize (@raw_set_WellFormed uv e s).
        unfold raw_set. rewrite H.
        intro XXX. specialize (XXX _ eq_refl). eauto. }
      { intros.
        consider (nth_error_get_hlist_nth (typD nil) tus uv).
        { destruct s0. intros.
          assert (t = x).
          { apply nth_error_get_hlist_nth_Some in H4. simpl in *.
            forward_reason. congruence. }
          subst.
          eapply exprD'_instantiate with (tvs' := nil) (tvs := tvs) in H3.
          2: eapply sem_preserves_if_raw_substD; eassumption.
          simpl in H3.
          forward_reason.
          eapply raw_substD_instantiate'
            with (f := fun u' : uvar =>
                          if uv ?[ eq ] u' then Some (raw_subst s 0 e) else None)
                 (P := fun us vs => x0 us vs = t0 us)
                 in H2.
          { forward_reason.
            eapply raw_substD_add in H2; eauto.
            { forward_reason.
              eexists; split. eapply H2.
              intros.
              rewrite H7 in H8; clear H7.
              forward_reason.
              rewrite H6 in H7; clear H6; eauto.
              split; auto.
              specialize (H5 us vs Hnil).
              simpl in H5. rewrite H5; eauto.
              rewrite <- H8; clear H8.
              eapply nth_error_get_hlist_nth_Some in H4; simpl in H4.
              forward_reason. rewrite H4.
              clear - EqDec_eq_typ.
              match goal with
                | |- ?X = match _ with eq_refl => match _ with eq_refl => ?Y end end =>
                  change Y with X ; generalize X
              end.
              destruct x3. rewrite (UIP_refl pf). reflexivity. }
            { unfold raw_lookup.
              rewrite FACTS.map_o.
              unfold raw_lookup in H0. rewrite H0. reflexivity. } }
          { red. intros.
            forward. inv_all; subst.
            change_rewrite H7 in H4.
            inv_all; subst.
            eexists; split. eapply H3. intuition. } }
        { intro. exfalso.
           clear - pf H4.
           eapply nth_error_get_hlist_nth_None in H4.
           congruence. } }
    Qed.

    Lemma length_S_last
    : forall T (ls : list T) n,
        S n = length ls ->
        exists l ls', ls = ls' ++ l :: nil /\ n = length ls'.
    Proof.
      clear. intros.
      destruct (@exists_last _ ls).
      { destruct ls. inversion H. congruence. }
      { destruct s. exists x0. exists x. split; auto.
        cut (length ls = length (x ++ x0 :: nil)).
        rewrite <- H. rewrite app_length. simpl.
        rewrite Plus.plus_comm. inversion 1. reflexivity.
        f_equal. assumption. }
    Qed.

    Theorem hlist_app_hlist_map
    : forall T (F G : T -> Type) (f : forall x, F x -> G x) ls ls'
             (a : hlist F ls) (b : hlist F ls'),
        hlist_map f (hlist_app a b) =
        hlist_app (hlist_map f a) (hlist_map f b).
    Proof.
      clear.
      induction a. simpl; auto.
      simpl. intros. f_equal. auto.
    Qed.

    Lemma substD_pull
    : forall (s s' : raw) (u n : nat),
        raw_pull u n s = Some s' ->
        WellFormed_subst s ->
        WellFormed_subst s' /\
        (forall (tus tus' : list typ) (tvs : tenv typ)
                (sD : hlist (typD nil) (tus ++ tus') -> hlist (typD nil) tvs -> Prop),
           u = length tus ->
           n = length tus' ->
           substD (tus ++ tus') tvs s = Some sD ->
           exists sD' : hlist (typD nil) tus -> hlist (typD nil) tvs -> Prop,
             substD tus tvs s' = Some sD' /\
             (exists
                 (eus' : list expr) (us' : hlist
                                             (fun t : typ =>
                                                hlist (typD nil) tus ->
                                                hlist (typD nil) tvs -> typD nil t)
                                             tus'),
                 hlist_build
                   (fun t : typ =>
                      hlist (typD nil) tus -> hlist (typD nil) tvs -> typD nil t)
                   (fun (t : typ) (e : expr) => exprD' tus tvs e t) tus' eus' =
                 Some us' /\
                 (forall (us : hlist (typD nil) tus) (vs : hlist (typD nil) tvs),
                    let us'0 :=
                        hlist_map
                          (fun (t : typ)
                               (x : hlist (typD nil) tus ->
                                    hlist (typD nil) tvs -> typD nil t) =>
                             x us vs) us' in
                    sD' us vs -> sD (hlist_app us us'0) vs))).
    Proof.
      intros s s' u n; revert s s' u.
      induction n.
      { simpl. intros. inv_all; subst.
        split; eauto. intros. subst.
        destruct tus'; simpl in *; try congruence.
        clear H1.
        admit. }
      { simpl. intros.
        forward.
        eapply IHn in H1; clear IHn.
        { forward_reason.
          split; eauto.
          { intros. subst.
            eapply length_S_last in H4.
            destruct H4 as [ ? [ ? [ ? ? ] ] ].
            subst.
            assert (exists sD',
                      raw_substD (tus ++ x0) tvs (FM.remove (length tus + length x0) s) = Some sD' /\
                      forall us us' u vs,
                        sD' (hlist_app us us') vs <->
                        sD (hlist_app us (hlist_app us' (Hcons u Hnil))) vs).
            { admit. }
            destruct H3 as [ ? [ ? ? ] ].
            specialize (H2 _ _ _ _ eq_refl eq_refl H3).
            forward_reason.
            eexists. split. eassumption.
            eexists (x3 ++ e :: nil).
            eapply substD_lookup in H; eauto.
            forward_reason.
            assert (tus ++ x0 ++ x :: nil = (tus ++ x0) ++ x :: nil).
            { admit. }
            assert (exprD' ((tus ++ x0) ++ x :: nil) tvs e x5 =
                    Some match H9 in _ = t return hlist _ t -> _ -> _ with
                           | eq_refl => x6
                         end).
            { revert H. clear.
              generalize dependent (tus ++ x0 ++ x :: nil).
              destruct H9. auto. }
            clear H.
            assert (x5 = x) by admit.
            subst.
            eapply exprD'_strengthen_last in H10; [ | admit ].
            forward_reason.
            exists (hlist_app x4
                              (Hcons (fun us vs => x5 (hlist_app us (hlist_map (fun t (x : hlist _ tus -> hlist _ tvs -> typD nil t) => x us vs) x4)) vs) Hnil)).
            split.
            { eapply hlist_build_app_only_if; eauto.
              simpl. admit. }
            { intros. eapply H7 in H11; clear H7.
              rewrite hlist_app_hlist_map. simpl.
              eapply H4 in H11; clear H4. eapply H11. } } }
        { admit. } }
    Qed.

    Instance SubstUpdateOk_subst : SubstUpdateOk SubstUpdate_subst _ :=
    {| WellFormed_empty := WellFormed_empty
     ; substD_empty := substD_empty
     ; set_sound := substD_set
     ; pull_sound := substD_pull
     |}.

  End exprs.
End Make.

Require MirrorCore.Subst.UVarMap.

Module SUBST := Make UVarMap.MAP.
