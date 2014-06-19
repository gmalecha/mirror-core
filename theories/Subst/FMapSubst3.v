Require Coq.FSets.FMapFacts.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Bool.
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

    (** TODO(gmalecha): I have to eliminate the proofs here!
     ** The FMapInterface does not support this!
     **)
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
      else let s := FM.add u v' s in
           let s := FM.map (raw_subst s 0) s in
           Some s.

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

(*
    Lemma normalized_lift : forall s n e,
                              normalized s e <-> normalized s (lift 0 n e).
    Proof.
      unfold normalized. intuition.
      rewrite mentionsU_lift in *. eauto.
      eapply H. rewrite mentionsU_lift; eauto. eauto.
    Qed.
*)

    (* mentionsU and instantiate

    Lemma mentionsU_raw_subst_n_irr : forall u s e n n',
      mentionsU u (raw_subst s n e) = mentionsU u (raw_subst s n' e).
    Proof.
      induction e; simpl; intros; auto.
      { rewrite (IHe1 n n'). rewrite (IHe2 n n'). auto. }
      { destruct (raw_lookup u0 s); auto.
        repeat rewrite mentionsU_lift. auto. }
    Qed.
*)

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
          { generalize (@FM.empty_1 expr).
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

    Definition subst_set (u : uvar) (e : expr) (s : subst) : option subst :=
      match raw_set u e s.(env) as v return raw_set u e s.(env) = v -> option subst with
        | None => fun _ => None
        | Some s' => fun pf => Some {| env := s'
                                     ; wf := @raw_set_WellFormed _ _ _ _ pf s.(wf) |}
      end eq_refl.

(*
    Definition subst_substD us vs (sub : subst) : Prop :=
      raw_substD us vs sub.(env).
*)

(*
    Definition subst_WellTyped tus tvs (sub : subst) : Prop :=
      raw_WellTyped tus tvs sub.(env).
*)

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
      intros.
      unfold raw_substD in *.
      match goal with
        | H : FM.fold _ _ (Some ?X) = _ |- _ =>
          generalize dependent X
      end.
      revert sD.
      generalize dependent s. intro s.
      intro H.
      eapply PROPS.map_induction with (m := s).
      { simpl; intros.
        exfalso. clear - H0 H1.
        unfold raw_lookup in H1.
        red in H0.
        eapply FM.find_2 in H1.
        eapply H0. eauto. }
      { intros.
        generalize H2.
        match goal with
          | H : FM.fold ?F _ ?R = _ |- _ =>
            eapply PROPS.fold_Add
            with (eqA := fun (a b : option (hlist _ tus -> hlist _ tvs -> Prop)) =>
                           match a , b with
                             | None , None => True
                             | Some a , Some b =>
                               forall us vs, a us vs <-> b us vs
                             | _ , _ => False
                           end)
                   (f := F) (i := R) in H2
        end; eauto.
        { simpl in H3. unfold raw_lookup in H3.
          intro. red in H5.
          rewrite H5 in H3; clear H5.
          erewrite FACTS.add_o in H3.
          consider (FM.E.eq_dec x uv).
          { red in e1. intros; inv_all; subst.
            progress forward.
            inv_all; subst.
            eapply nth_error_get_hlist_nth_Some in H6; simpl in *;
            forward_reason.
            do 3 eexists; split; eauto.
            instantiate (1 := eq_sym x0).
            intros. eapply H5 in H4; clear H5.
            destruct H4.
            rewrite <- H4. rewrite H3. clear.
            destruct x0. reflexivity. }
          { intro. forward; inv_all; subst.
            specialize (H0 H3 _ _ H9); clear H2 H9.
            forward_reason.
            do 3 eexists; split; eauto.
            intros. eapply H2.
            apply H6 in H4; intuition. } }
        { constructor; repeat red; intros; subst.
          destruct x0; intuition.
          destruct x0; destruct y; auto. symmetry; auto.
          destruct x0; destruct y; destruct z; intuition.
          eapply H6. eapply H5. auto.
          eapply H5. eapply H6. auto. }
        { clear. repeat red. simpl; intros.
          match goal with
            | |- match match ?X with _ => _ end with _ => _ end =>
              change X with (nth_error_get_hlist_nth (typD nil) tus x)
          end.
          subst.
          forward.
          destruct (nth_error_get_hlist_nth (typD nil) tus y);
            forward.
          subst.
          destruct x1; destruct y1; auto.
          intros. rewrite H1. reflexivity. }
        { clear. red; intros.
          repeat match goal with
                   | |- context [ match ?X with _ => _ end ] =>
                     match X with
                       | match _ with _ => _ end => fail 1
                       | _ => consider X; intros
                     end
                 end; auto.
          subst. intuition. } }
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
        (forall (us : hlist (typD nil) tus) (vs : hlist (typD nil) tvs), P us vs).
    Proof.
      clear. simpl; intros.
      unfold raw_substD.
      rewrite FM.fold_1.
      cutrewrite (FM.elements (FM.empty expr) = nil).
      { simpl. eexists; split; eauto. simpl. auto. }
      { apply PROPS.elements_Empty.
        eapply FM.empty_1. }
    Qed.
(*
    Lemma raw_substD_add
    : forall tus tvs uv e s,
        raw_lookup uv s = None ->
        exprD' tus tvs e t
        raw_substD tus tvs (FM.add uv e s) = Some sD ->
        exists sD',
          raw_substD tus tvs s = Some sD' /\
          exists x,
            nth_error_get_hlist_nth _ tus uv = Some x /\
            forall us vs,
              sD us vs <->
              exprD (join_env us) (join_env vs) tvs e (projT1 x) = Some (projT2 x).
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
*)

    Lemma raw_substD_iff
    : forall (tus tvs : tenv typ) s sD,
        (exists sD',
           raw_substD tus tvs s = Some sD' /\
           forall us vs, sD us vs <-> sD' us vs) <->
        (forall uv e,
           raw_lookup uv s = Some e ->
           exists ty val get,
             nth_error_get_hlist_nth _ tus uv = Some (@existT _ _ ty get) /\
             exprD' tus tvs e ty = Some val /\
             forall us vs,
               sD us vs ->
               get us = val us vs).
    Proof.
(*
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
*)
    Admitted.

    Lemma raw_substD_map
    : forall tus tvs f s sD,
        (forall uv e x val,
           raw_lookup uv s = Some e ->
           nth_error tus uv = Some x ->
           exprD' tus tvs (f e) x = Some val ->
           exists val',
             exprD' tus tvs e x = Some val' /\
             forall us vs, val us vs = val' us vs) ->
        raw_substD tus tvs (FM.map f s) = Some sD ->
        exists sD',
          raw_substD tus tvs s = Some sD' /\
          forall us vs,
            sD us vs <-> sD' us vs.
    Proof.
      intros.
      assert (exists sD' : hlist (typD nil) tus -> hlist (typD nil) tvs -> Prop,
       raw_substD tus tvs (FM.map f s) = Some sD' /\
       (forall (us : hlist (typD nil) tus) (vs : hlist (typD nil) tvs),
        sD us vs <-> sD' us vs)).
      { eexists. split; eauto. reflexivity. }
      generalize (proj1 (@raw_substD_iff _ _ _ _) H1); clear H1; intro.
      eapply raw_substD_iff.
      intros.
      intros. specialize (H1 uv (f e)).
      unfold raw_lookup in *.
      rewrite FACTS.map_o in H1. rewrite H2 in *.
      specialize (H1 eq_refl).
      forward_reason.
      generalize H1.
      apply nth_error_get_hlist_nth_Some in H1. forward_reason.
      simpl in *.
      eapply H in H2; eauto.
      forward_reason. intros. do 3 eexists; split; eauto.
      split; eauto.
      intros. rewrite <- H5. eauto.
    Qed.
(*
    Theorem substD_set
    : forall (uv : nat) (e : expr _) (s s' : subst) u v,
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
*)

    Lemma substD_set
    : forall (uv : nat) (e : expr) (s s' : raw),
        set uv e s = Some s' ->
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
      { admit. }
      { intros. admit. }
    Qed.

(*
    Lemma raw_pull_raw_pull_lem
    : forall c f c' s,
        raw_pull f (c + c') s = match raw_pull f c s with
                                  | None => None
                                  | Some s => raw_pull (c + f) c' s
                                end.
    Proof.
      clear.
      induction c; intros.
      { simpl. auto. }
      { simpl. forward. rewrite IHc.
        replace (c + S f) with (S (c + f)) by omega. reflexivity. }
    Qed.

    Lemma find_after_pull'
    : forall T  f c s x (X : T) Y Z,
        match raw_pull' f c s with
          | Some s => match FM.find (f + c + x) s with
                        | None => Z
                        | Some _ => Y s
                      end
          | None => X
        end =
        match FM.find (f + c + x) s with
          | Some _ => match raw_pull' f c s with
                        | None => X
                        | Some s => Y s
                      end
          | None => match raw_pull' f c s with
                      | None => X
                      | Some s => Z
                    end
        end.
    Proof.
      clear.
      induction c; intros.
      { simpl. reflexivity. }
      { simpl.
        destruct (FM.find (f + c) s).
        { replace (f + S c + x) with (f + c + S x) by omega.
          rewrite IHc.
          rewrite FACTS.remove_neq_o. reflexivity.
          omega. }
        { forward. } }
    Qed.

    Inductive R_option T (R : T -> T -> Prop) : option T -> option T -> Prop :=
    | R_option_None : R_option R None None
    | R_option_Some : forall x y, R x y -> R_option R (Some x) (Some y).

    Lemma pull_sem
    : forall n f s s',
        raw_pull f n s = Some s' ->
        (forall u,
           raw_lookup u s' =
           if u ?[ lt ] f then raw_lookup u s
           else if u ?[ lt ] (f + n) then None
                else raw_lookup u s).
    Proof.
      clear.
      induction n; simpl.
      { intros. inv_all; subst.
        replace (f + 0) with f by omega.
        destruct (u ?[ lt ] f); reflexivity. }
      { intros.
        forward. eapply IHn with (u := u) in H0.
        rewrite H0. unfold raw_lookup in *.
        consider (u ?[ lt ] f); intros.
        { consider (u ?[ lt ] S f).
          { intros. rewrite FACTS.remove_neq_o. reflexivity. omega. }
          { intros. exfalso. omega. } }
        { consider (u ?[ lt ] S f).
          { intros. assert (u = f). clear - H1 H0.
            destruct (Compare_dec.lt_eq_lt_dec u f); auto.
            { destruct s. exfalso; omega. auto. }
            { exfalso; omega. }
            { subst. consider (f ?[ lt ] (f + S n)).
              { intros. rewrite FACTS.remove_eq_o; auto. }
              { intros. exfalso; omega. } } }
          { intros.
            replace (S f + n) with (f + S n) in * by omega.
            consider (u ?[ lt ] (f + S n)); auto.
            intros. rewrite FACTS.remove_neq_o. reflexivity. omega. } } }
    Qed.

    Lemma pull_get_exprs
    : forall f c s s',
        raw_pull f c s = Some s' ->
        exists ls, length ls = c /\
                   (forall n, n < c ->
                              exists e,
                                nth_error ls n = Some e /\
                                raw_lookup (f + n) s = Some e).
    Proof.
      clear. admit.
    Qed.

    Lemma raw_pull_raw_pull'
    : forall c f c' s,
        R_option (FM.Equal) (raw_pull f (c + c') s) (raw_pull' f c s).
    Proof.
    Admitted.
*)


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
