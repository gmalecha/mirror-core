Require Coq.FSets.FMapFacts.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Bool.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.VariablesI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Util.Forwardy.

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
    Context {Expr_expr : Expr _ expr}.
    Context {ExprOk_expr : ExprOk Expr_expr}.
    Context {ExprUVar_expr : ExprUVar expr}.
    Context {ExprUVarOk_expr : ExprUVarOk ExprUVar_expr}.

    Definition raw : Type := FM.t expr.

    Definition normalized (this : raw) (e : expr) : Prop :=
      forall u, mentionsU u e = true -> ~FM.In u this.

    Definition WellFormed (this : raw) : Prop :=
      forall (k : uvar) e,
        FM.MapsTo k e this ->
        normalized this e.

    Definition raw_lookup : uvar -> raw -> option expr :=
       @FM.find _.

    Definition raw_subst (s : raw) : nat -> expr -> expr :=
      instantiate (fun x => raw_lookup x s).

    Definition raw_instantiate (f : uvar -> option expr) (s : raw) : raw :=
      FM.map (instantiate f 0) s.

    Definition raw_set (u : uvar) (e : expr) (s : raw) : option raw :=
      let v' := raw_subst s 0 e in
      if mentionsU u v'
      then None
      else let s :=
               FM.add u v' (raw_instantiate (fun u' => if u ?[ eq ] u' then
                                                         Some v'
                                                       else None) s)
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

    (* normalized and instantiate *)
    Lemma wf_instantiate_normalized : forall s e n,
      WellFormed s ->
      normalized s (raw_subst s n e).
    Proof.
      unfold WellFormed, normalized, raw_subst. intros.
      eapply mentionsU_instantiate in H0; eauto.
      destruct H0.
      { destruct H0. unfold raw_lookup in H0.
        eapply FACTS.not_find_in_iff. assumption. }
      { forward_reason.
        eapply H. 2: eassumption.
        eapply FACTS.find_mapsto_iff. eapply H0. }
    Qed.

    Definition raw_substD (tus tvs : list typ) (sub : raw)
    : option (hlist typD tus -> hlist typD tvs -> Prop) :=
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

    Lemma mentionsU_subst : forall s u x n,
      mentionsU u (raw_subst s n x) = true <->
      (mentionsU u x = true /\ ~FM.In u s \/
       exists u' e',
         FM.MapsTo u' e' s /\
         mentionsU u' x = true /\
         mentionsU u e' = true).
    Proof.
      intros. unfold raw_subst.
      generalize (@mentionsU_instantiate _ _ _ _ ExprUVar_expr _); eauto.
      unfold mentionsU_instantiate_spec. intros.
      rewrite H.
      unfold raw_lookup.
      rewrite <- FACTS.not_find_in_iff.
      intuition.
      { right. forward_reason. do 2 eexists.
        intuition eauto. }
      { right. forward_reason. do 2 eexists.
        intuition eauto.
        apply FACTS.find_mapsto_iff. assumption. }
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
        + subst. eapply mentionsU_instantiate in H2; eauto.
          destruct H2.
          - forward.
          - forward_reason. forward.
        + unfold raw_instantiate in H4.
          rewrite FACTS.map_in_iff in H4.
          eapply mentionsU_instantiate in H2; eauto.
          destruct H2; forward_reason; forward.
          - eapply H0 in H3. red in H3. eapply H3 in H5; eauto.
          - inv_all. subst.
            eapply mentionsU_instantiate in H6; eauto.
            destruct H6; forward_reason.
            * unfold raw_lookup in H2.
              apply FACTS.not_find_in_iff in H2. auto.
            * unfold raw_lookup in H2.
              eapply FM.find_2 in H2.
              eapply H0 in H2. red in H2.
              eapply H2 in H7. auto. }
    Qed.

    Instance Subst_subst : Subst raw expr :=
    { subst_lookup := raw_lookup
    ; subst_domain := fun x => List.map (@fst _ _) (FM.elements x)
    }.

    Definition raw_drop (from : nat) (sub : raw) : option raw :=
      match FM.find from sub with
        | None => None
        | Some _ => Some (FM.remove from sub)
      end.

    Fixpoint mentionsRange (m : nat -> expr -> bool) (from len : nat) (e : expr) : bool :=
      match len with
        | 0 => false
        | S n => if m from e then true else mentionsRange m (S from) n e
      end.

    Definition raw_forget (u : nat) (r : raw) : raw * option expr :=
      match FM.find u r with
        | None => (r,None)
        | Some e => (FM.remove u r, Some e)
      end.

    Definition raw_strengthenU (from len : nat) (s : raw) : bool :=
      FM.fold (fun k e (a : bool) =>
                 if from ?[ le ] k && k ?[ lt ] (from + len) then
                   if a then
                     mentionsRange mentionsU from len e
                   else false
                 else
                   true)
              s true.

(*
    Definition raw_strengthenV (from len : nat) (s : raw) : bool :=
      FM.fold (fun k e (a : bool) =>
                 if a then
                   mentionsRange mentionsV from len e
                 else false)
              s true.
*)

    Instance SubstUpdate_subst : SubstUpdate raw expr :=
    { subst_set := raw_set
(*
    ; subst_empty := FM.empty _
    ; forget := raw_forget
    ; strengthenU := raw_strengthenU
    ; strengthenV := raw_strengthenV
*)
    }.

    Lemma None_becomes_None
    : forall tus tvs l, fold_left
         (fun
            (a0 : option
                    (hlist typD tus -> hlist typD tvs -> Prop))
            (p : FM.key * expr) =>
          match nth_error_get_hlist_nth typD tus (fst p) with
          | Some (existT T get) =>
              match exprD' tus tvs (snd p) T with
              | Some val' =>
                  match a0 with
                  | Some P1 =>
                      Some
                        (fun (us : hlist typD tus)
                           (vs : hlist typD tvs) =>
                         get us = val' us vs /\ P1 us vs)
                  | None => None
                  end
              | None => None
              end
          | None => None
          end) l None = None.
    Proof.
      clear. induction l; simpl; auto.
      match goal with
        | |- _ _ _ ?X = _ =>
          cutrewrite (X = None); [ assumption | ]
      end.
      repeat match goal with
               | |- match ?X with _ => _ end = _ =>
                 destruct X; try reflexivity
             end.
    Qed.

    Lemma substD_weaken
    : forall (tus tvs : tenv typ) (tus' tvs' : list typ) (s : raw)
             (sD : hlist typD tus -> hlist typD tvs -> Prop),
        raw_substD tus tvs s = Some sD ->
        exists
          sD' : hlist typD (tus ++ tus') ->
                hlist typD (tvs ++ tvs') -> Prop,
          raw_substD (tus ++ tus') (tvs ++ tvs') s = Some sD' /\
          (forall (us : hlist typD tus) (us' : hlist typD tus')
                  (vs : hlist typD tvs) (vs' : hlist typD tvs'),
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
              remember X ; remember Y
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
        forwardy. inv_all; subst.
        eapply nth_error_get_hlist_nth_weaken with (ls' := tus') in H0.
        simpl in *.
        eapply exprD'_weaken with (tus' := tus') (tvs' := tvs') in H2; eauto with typeclass_instances.
        forward_reason.
        Cases.rewrite_all_goal.
        eapply IHl in H1; eauto with typeclass_instances.
        clear H1. intros. simpl.
        erewrite H; clear H. erewrite H3; clear H3.
        erewrite H4; clear H4. reflexivity. }
    Qed.

    Definition eq_option_A tus tvs
        (x y : option (hlist typD tus -> hlist typD tvs -> Prop))
    : Prop :=
           match x with
             | Some x0 =>
               match y with
                 | Some y0 =>
                   forall (a : hlist typD tus) (b : hlist typD tvs),
                     x0 a b <-> y0 a b
                 | None => False
               end
             | None => match y with
                         | Some _ => False
                         | None => True
                       end
           end.

    Theorem eq_option_A_Roption tus tvs
    : forall x y, eq_option_A x y <-> (Roption (RexprT tus tvs iff)) x y.
    Proof.
      clear. split; intros.
      { red in H. destruct x; destruct y; intuition; constructor.
        do 5 red. intros.
        apply equiv_eq_eq in H0.
        apply equiv_eq_eq in H1. subst. auto. }
      { red. inversion H; auto.
        subst. intros. eapply H0; reflexivity. }
    Qed.

    Theorem Proper_substD
    : forall tus tvs,
        Proper (eq ==> eq ==> @eq_option_A tus tvs ==> @eq_option_A tus tvs)
               (fun (k : FM.key) (v : expr)
                    (P : option (hlist typD tus -> hlist typD tvs -> Prop)) =>
                  match nth_error_get_hlist_nth typD tus k with
                    | Some (existT T get) =>
                      match exprD' tus tvs v T with
                        | Some val' =>
                          match P with
                            | Some P0 =>
                              Some
                                (fun (us : hlist typD tus)
                                     (vs : hlist typD tvs) =>
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
      { subst. forward. rewrite H1. intuition. }
      { subst. forward. }
    Qed.

    Lemma Transpose_substD
    : forall tus tvs,
        PROPS.transpose_neqkey
          (@eq_option_A tus tvs)
          (fun (k : FM.key) (v : expr)
               (P : option (hlist typD tus -> hlist typD tvs -> Prop)) =>
             match nth_error_get_hlist_nth typD tus k with
               | Some (existT T get) =>
                 match exprD' tus tvs v T with
                   | Some val' =>
                     match P with
                       | Some P0 =>
                         Some
                           (fun (us : hlist typD tus)
                                (vs : hlist typD tvs) =>
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
                   | _ => destruct X; try constructor
                 end
             end.
      intuition. intuition.
    Qed.

    Local Instance Equivalence_substD tus tvs
    : Equivalence (@eq_option_A tus tvs).
    Proof.
      unfold eq_option_A.
      clear. constructor; red; intros.
      { forward. }
      { forward. firstorder. }
      { destruct x; destruct y; destruct z; auto.
        intros. etransitivity. eapply H. eauto.
        intuition. }
    Qed.

    Lemma Proper_amap_substD tus tvs
    : Proper (FM.Equal ==> @eq_option_A tus tvs) (raw_substD tus tvs).
    Proof.
      red. red.
      unfold raw_substD.
      intros. eapply PROPS.fold_Equal; eauto.
      { eauto with typeclass_instances. }
      { eapply Proper_substD. }
      { eapply Transpose_substD. }
    Qed.

    Lemma substD_lookup'
    : forall (s : raw) (uv : nat) (e : expr),
        raw_lookup uv s = Some e ->
        forall tus tvs sD,
          raw_substD tus tvs s = Some sD ->
          exists t val get,
            nth_error_get_hlist_nth _ tus uv = Some (@existT _ _ t get) /\
            exprD' tus tvs e t = Some val /\
            forall us vs,
              sD us vs ->
              get us = val us vs.
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
            forwardy.
            inv_all; subst.
            do 3 eexists; split; eauto.
            split; eauto.
            intros. eapply H2 in H6. intuition. }
          { intro.
            change_rewrite H3 in H1.
            red in H1.
            forwardy; inv_all; subst.
            specialize (H H2 _ _ H6); clear H2 H6.
            forward_reason.
            do 3 eexists; split; eauto.
            split; eauto.
            intros. eapply H4 in H7.
            intuition. } } }
    Qed.

    Lemma substD_lookup
    : forall s uv e,
        WellFormed s ->
        raw_lookup uv s = Some e ->
        forall tus tvs sD,
          raw_substD tus tvs s = Some sD ->
          exists t val get,
            nth_error_get_hlist_nth _ tus uv = Some (@existT _ _ t get) /\
            exprD' tus tvs e t = Some val /\
            forall us vs,
              sD us vs ->
              get us = val us vs.
    Proof.
      intros; eapply substD_lookup'; eauto.
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

    Lemma normalized_fmapsubst
    : forall (s : raw) (e : expr) (u : nat),
        WellFormed s ->
        raw_lookup u s = Some e ->
        forall (u' : nat) (e' : expr),
          raw_lookup u' s = Some e' -> mentionsU u' e = false.
    Proof.
      unfold WellFormed, normalized, raw_lookup; simpl; intros.
      eapply FM.find_2 in H1.
      eapply FM.find_2 in H0.
      consider (mentionsU u' e); auto.
      intros. exfalso.
      eapply H in H0.
      eapply H0.
      red. eexists. eauto. eauto.
    Qed.

    Instance SubstOk_subst : SubstOk Subst_subst :=
    {| WellFormed_subst := WellFormed
     ; substD := raw_substD
(*     ; substD_weaken := substD_weaken *)
     ; substD_lookup := substD_lookup
     ; WellFormed_domain := WellFormed_domain
     ; lookup_normalized := normalized_fmapsubst
     |}.

    Definition raw_empty : raw := FM.empty expr.

    Lemma WellFormed_empty : WellFormed_subst raw_empty.
    Proof.
      compute. intros.
      eapply FACTS.empty_mapsto_iff. eauto.
    Qed.

    Lemma substD_empty
    : forall tus tvs : tenv typ,
      exists P : hlist typD tus -> hlist typD tvs -> Prop,
        substD tus tvs raw_empty = Some P /\
        (forall (us : hlist typD tus) (vs : hlist typD tvs),
           P us vs).
    Proof.
      clear. simpl; intros.
      unfold raw_substD.
      rewrite FM.fold_1.
      cutrewrite (FM.elements raw_empty = nil).
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

    Lemma raw_substD_instantiate_ho
    : forall tus tvs s sD f P (ExprTApp : CtxLogic.ExprTApplicative P),
        sem_preserves_if_ho P f ->
        raw_substD tus tvs s = Some sD ->
        exists sD',
          raw_substD tus tvs (FM.map (instantiate f 0) s) = Some sD' /\
          P (fun us vs => sD' us vs <-> sD us vs).
    Proof.
      unfold raw_substD. intros.
      cut (exists sD' : hlist typD tus -> hlist typD tvs -> Prop,
             FM.fold
               (fun (k : FM.key) (v : expr)
                    (P : option (hlist typD tus -> hlist typD tvs -> Prop)) =>
                  let v := instantiate f 0 v in
                  match nth_error_get_hlist_nth typD tus k with
                    | Some (existT T get) =>
                      match exprD' tus tvs v T with
                        | Some val' =>
                          match P with
                            | Some P0 =>
                              Some
                                (fun (us : hlist typD tus)
                                     (vs : hlist typD tvs) =>
                                   get us = val' us vs /\ P0 us vs)
                            | None => None
                          end
                        | None => None
                      end
                    | None => None
                  end) s
               (Some
                  (fun (_ : hlist typD tus) (_ : hlist typD tvs) => True)) =
             Some sD' /\
             P (fun us vs => sD' us vs <-> sD us vs)).
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
        forwardy.
        eexists; split; eauto.
        generalize H2. eapply CtxLogic.exprTAp.
        eapply CtxLogic.exprTPure.
        clear - H4. intros; etransitivity; eauto. }
      { revert H0. revert sD.
        match goal with
          | |- forall x, FM.fold ?F _ ?X = _ ->
               exists y, FM.fold ?G _ ?Y = _ /\ _ =>
            eapply PROPS.fold_rel with (m := s) (f := F) (g := G)
        end.
        { intros. inv_all; subst.
          eexists; split; eauto.
          eapply CtxLogic.exprTPure. reflexivity. }
        { intros.
          forwardy. inv_all; subst.
          specialize (H1 _ eq_refl).
          forward_reason. subst.
          change_rewrite H2.
          eapply (@instantiate_sound_ho _ _ _ _ ExprUVar_expr _ _ _ _ _ nil) in H3; eauto.
          forward_reason. simpl in *.
          change_rewrite H1.
          eexists; split; [ reflexivity | ].
          generalize H3; clear H3. eapply CtxLogic.exprTAp.
          generalize H4; clear H4. eapply CtxLogic.exprTAp.
          eapply CtxLogic.exprTPure.
          intros. rewrite H3.
          specialize (H4 Hnil). simpl in H4.
          rewrite H4. reflexivity. } }
    Qed.

    Lemma raw_substD_instantiate
    : forall tus tvs s sD f P,
        sem_preserves_if P f ->
        raw_substD tus tvs s = Some sD ->
        exists sD',
          raw_substD tus tvs (FM.map (instantiate f 0) s) = Some sD' /\
          forall us vs, P us vs -> (sD' us vs <-> sD us vs).
    Proof.
      intros.
      eapply raw_substD_instantiate_ho in H; eauto.
      eapply CtxLogic.ExprTApplicative_foralls_impl.
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
      forwardy.
      eexists; split. eapply H4.
      intros. rewrite H5; clear H5.
      clear. tauto.
    Qed.

    Theorem substD_set
    : forall (uv : nat) (e : expr) (s s' : raw),
        raw_set uv e s = Some s' ->
        WellFormed s ->
        WellFormed s' /\
        (raw_lookup uv s = None ->
        forall (tus tvs : tenv typ) (t : typ)
               (val : exprT tus tvs (typD t))
               (get : hlist typD tus -> typD t)
               (sD : exprT tus tvs Prop),
           raw_substD tus tvs s = Some sD ->
           nth_error_get_hlist_nth typD tus uv =
           Some
             (existT
                (fun t0 : typ => hlist typD tus -> typD t0) t
                get) ->
           exprD' tus tvs e t = Some val ->
           exists sD' : exprT tus tvs Prop,
             raw_substD tus tvs s' = Some sD' /\
             (forall (us : hlist typD tus) (vs : hlist typD tvs),
                sD' us vs <-> (sD us vs /\ get us = val us vs))).
    Proof.
      simpl; intros. unfold raw_set in *.
      forward. inv_all; subst.
      split.
      { generalize (@raw_set_WellFormed uv e s).
        unfold raw_set. rewrite H.
        intro XXX. specialize (XXX _ eq_refl). eauto. }
      { intros.
        eapply (@instantiate_sound _ _ _ _ _ _ _ _ _ _ nil) in H4; eauto.
        2: eapply sem_preserves_if_substD; eassumption.
        simpl in H4.
        forward_reason.
        eapply raw_substD_instantiate
          with (f := fun u' : uvar =>
                     if uv ?[ eq ] u' then Some (raw_subst s 0 e) else None)
               (P := fun us vs => x us vs = get us)
          in H2.
        forward_reason.
        eapply raw_substD_add in H2; eauto.
        { forward_reason.
          eexists; split; [ eapply H2 | ].
          intros.
          rewrite H7.
          clear - H7 H5 H6.
          specialize (H6 us vs).
          specialize (H5 us vs).
          specialize (H7 us vs).
          split; intros.
          { assert (x1 us vs) by tauto.
            clear H7.
            cut (sD us vs).
            + intuition. rewrite H3. symmetry.
              eapply (H5 Hnil). auto.
            + intuition. symmetry in H2. tauto. }
          { simpl in *. destruct H.
            rewrite H0.
            specialize (H5 Hnil). simpl in H5.
            rewrite H5 in H0; auto.
            symmetry in H0. tauto. } }
        { unfold raw_lookup.
          rewrite FACTS.map_o.
          unfold raw_lookup in H1. rewrite H1. reflexivity. }
        { do 2 red; intros.
          forward. inv_all; subst.
          change_rewrite H7 in H3.
          inv_all; subst.
          eexists; split; [ eapply H4 | ].
          intros. specialize (H5 us vs).
          auto. } }
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

    Lemma raw_substD_Equal
    : forall tus tvs s s' sD,
        raw_substD tus tvs s = Some sD ->
        FM.Equal s s' ->
        exists sD',
          raw_substD tus tvs s' = Some sD' /\
          forall us vs,
            sD us vs <-> sD' us vs.
    Proof.
      unfold raw_substD.
      intros.
      match goal with
        | _ : context [ FM.fold ?X _ ?A ] |- _ =>
          generalize (@PROPS.fold_Equal _ _ (@eq_option_A tus tvs) _ X
                                        (@Proper_substD _ _)
                                        (@Transpose_substD _ _) _ _ A H0)
      end.
      change_rewrite H.
      simpl. intros; forward.
      eexists; split; try eassumption. reflexivity.
    Qed.

    Lemma raw_substD_add'
    : forall tus tvs s k v sD,
        ~FM.In k s ->
        raw_substD tus tvs (FM.add k v s) = Some sD ->
        exists sD' t val get,
          raw_substD tus tvs s = Some sD' /\
          exprD' tus tvs v t = Some val /\
          nth_error_get_hlist_nth _ tus k = Some (@existT _ _ t get) /\
          forall us vs,
            sD us vs <->
            (sD' us vs /\ get us = val us vs).
    Proof.
      simpl. intros.
      unfold raw_substD in H0.
      match goal with
        | _ : context [ FM.fold ?X _ ?A ] |- _ =>
          generalize (@PROPS.fold_add _ _ (@eq_option_A tus tvs) _ X
                                      (@Proper_substD _ _)
                                      (@Transpose_substD _ _) s k v A H)
      end.
      change_rewrite H0.
      simpl. intros.
      forwardy.
      do 4 eexists.
      split; [ eassumption | ].
      split; [ eassumption | ].
      split; [ eassumption | ].
      inv_all; subst. intros.
      rewrite H2.
      intuition.
    Qed.

    Lemma WellFormed_remove
    : forall s k,
        WellFormed s ->
        WellFormed (FM.remove k s).
    Proof.
      unfold WellFormed. intros.
      red; intros.
      intro.
      eapply FACTS.remove_in_iff in H2.
      forward_reason; subst.
      red in H. eapply H; eauto.
      instantiate (1 := k0).
      eapply FACTS.remove_mapsto_iff in H0.
      intuition.
    Qed.

    Lemma raw_substD_strengthen_1
    : forall tus tu tvs s sD,
        ~FM.In (length tus) s ->
        (forall k e, FM.MapsTo k e s ->
                     mentionsU (length tus) e = false) ->
        raw_substD (tus ++ tu :: nil) tvs s = Some sD ->
        exists sD',
          raw_substD tus tvs s = Some sD' /\
          forall us vs val,
            sD (hlist_app us (Hcons val Hnil)) vs <-> sD' us vs.
    Proof.
      intros. revert H1.
      revert sD.
      unfold raw_substD.
      match goal with
        | |- forall x, FM.fold ?F _ ?X = _ ->
                       exists y, FM.fold ?G _ ?Y = _ /\ _ =>
          eapply PROPS.fold_rel with (m := s) (f := F) (g := G)
      end.
      { intros.
        inv_all; subst.
        eexists; split; eauto.
        simpl. reflexivity. }
      { intros. forward.
        inv_all; subst.
        specialize (H6 _ eq_refl).
        forward_reason. subst.
        eapply exprD'_strengthenU_single in H5; eauto.
        forward_reason.
        assert (k < length tus).
        { eapply nth_error_get_hlist_nth_Some in H4. simpl in *.
          destruct H4. clear H4.
          eapply nth_error_length_lt in x2.
          rewrite app_length in x2. simpl in *.
          destruct (Compare_dec.lt_eq_lt_dec k (length tus)) as [ [ ? | ? ] | ? ]; auto.
          - subst. exfalso. eapply H. red; eauto.
          - omega. }
        eapply nth_error_get_hlist_nth_appL with (F := typD) (tvs' := tu :: nil) in H6.
        forward_reason. change_rewrite H7.
        change_rewrite H6 in H4.
        inv_all; subst.
        simpl in *.
        rewrite H2.
        eexists; split; eauto. intros.
        rewrite H8; clear H8.
        rewrite H3; clear H3.
        rewrite H5. reflexivity. }
    Qed.

    Theorem substD_drop
    : forall (s s' : raw) (u : nat),
        raw_drop u s = Some s' ->
        WellFormed_subst s ->
        WellFormed_subst s' /\
        (forall (tus : list typ) (tu : typ) (tvs : tenv typ)
                (sD : hlist typD (tus ++ tu :: nil) ->
                      hlist typD tvs -> Prop),
           u = length tus ->
           raw_substD (tus ++ tu :: nil) tvs s = Some sD ->
           exists sD' : hlist typD tus -> hlist typD tvs -> Prop,
             raw_substD tus tvs s' = Some sD' /\
             (exists
                 (e : expr) (eD : hlist typD tus ->
                                  hlist typD tvs -> typD tu),
                 raw_lookup u s = Some e /\
                 exprD' tus tvs e tu = Some eD /\
                 (forall (us : hlist typD tus) (vs : hlist typD tvs),
                    sD' us vs <-> sD (hlist_app us (Hcons (eD us vs) Hnil)) vs))).
    Proof.
      simpl. unfold raw_drop.
      intros; forward.
      inv_all; subst.
      split.
      { eapply WellFormed_remove; assumption. }
      { intros. subst.
        assert (FM.Equal s (FM.add (length tus) e (FM.remove (length tus) s))).
        { red.
          intros. rewrite FACTS.add_o. rewrite FACTS.remove_o.
          destruct (FM.E.eq_dec (length tus) y); auto.
          red in e0. subst. assumption. }
        intros.
        eapply raw_substD_Equal in H1; [ | eassumption ].
        forward_reason.
        eapply raw_substD_add' in H1; eauto.
        forward_reason.
        eapply raw_substD_strengthen_1 in H1.
        { forward_reason.
          eexists; split; eauto.
          eapply nth_error_get_hlist_nth_appR in H5; simpl in H5.
          replace (length tus - length tus) with 0 in H5.
          forward_reason; inv_all; subst.
          subst.
          eapply exprD'_strengthenU_single in H4; try eassumption.
          { forward_reason.
            do 2 eexists.
            split; [ eassumption | ].
            split; [ eassumption | ].
            intros.
            rewrite <- H7 with (val := x1 us vs); clear H7.
            rewrite H3; clear H3.
            rewrite H6; clear H6.
            rewrite H8; clear H8.
            simpl. rewrite H5.
            intuition. }
          { do 2 red in H0.
            consider (mentionsU (length tus) e); try congruence.
            intro. exfalso.
            eapply H0. eapply FACTS.find_mapsto_iff in H.
            eassumption. eassumption.
            eapply FACTS.find_mapsto_iff in H.
            red. eauto. }
          { omega. }
          { omega. } }
        { rewrite FACTS.remove_in_iff.
          intro. intuition. }
        { intros.
          eapply FACTS.remove_mapsto_iff in H7.
          destruct H7.
          do 2 red in H0.
          consider (mentionsU (length tus) e0); try congruence.
          intro; exfalso.
          eapply H0. eassumption. eassumption.
          eapply FACTS.find_mapsto_iff in H.
          red; eauto. }
        { rewrite FACTS.remove_in_iff.
          clear. intuition. } }
    Qed.

    Theorem substD_drop'
    : forall (s s' : raw) (u : nat),
        raw_drop u s = Some s' ->
        WellFormed_subst s ->
        WellFormed_subst s' /\
        (exists e : expr,
           raw_lookup u s = Some e /\
           raw_lookup u s' = None /\
           (forall u' : nat, u' <> u -> raw_lookup u' s = raw_lookup u' s') /\
           (forall (tus : list typ) (tu : typ) (tvs : tenv typ)
                   (sD : hlist typD (tus ++ tu :: nil) ->
                         hlist typD tvs -> Prop),
              u = length tus ->
              raw_substD (tus ++ tu :: nil) tvs s = Some sD ->
              exists sD' : hlist typD tus -> hlist typD tvs -> Prop,
                raw_substD tus tvs s' = Some sD' /\
                (exists
                    eD : hlist typD tus -> hlist typD tvs -> typD tu,
                    exprD' tus tvs e tu = Some eD /\
                    (forall (us : hlist typD tus) (vs : hlist typD tvs),
                       sD' us vs <-> sD (hlist_app us (Hcons (eD us vs) Hnil)) vs)))).
    Proof.
      simpl. unfold raw_drop.
      intros; forward.
      inv_all; subst.
      split.
      { eapply WellFormed_remove; assumption. }
      { intros. subst.
        exists e.
        split; [ apply H | ].
        split.
        { unfold raw_lookup.
          rewrite FACTS.remove_o.
          destruct (FM.E.eq_dec u u); auto.
          exfalso. apply n; reflexivity. }
        split.
        { unfold raw_lookup.
          intros. rewrite FACTS.remove_o.
          destruct (FM.E.eq_dec u u'); auto.
          exfalso; auto. }
        { generalize (@substD_drop s (FM.remove u s) u).
          simpl. unfold raw_drop. rewrite H.
          intro XXX; specialize (XXX eq_refl H0).
          forward_reason; auto.
          intros.
          eapply H2 in H4; clear H2; eauto.
          forward_reason.
          eexists; split; eauto.
          unfold raw_lookup in H4.
          rewrite H in H4. inv_all; subst.
          eexists; split; eauto. } }
    Qed.

(*
    Theorem strengthenV_sound
    : forall (s : raw) (n c : nat),
        raw_strengthenV n c s = true ->
        WellFormed_subst s ->
        forall (tus : tenv typ) (tvs tvs' : list typ)
               (sD : hlist typD tus ->
                     hlist typD (tvs ++ tvs') -> Prop),
          substD tus (tvs ++ tvs') s = Some sD ->
          n = length tvs ->
          c = length tvs' ->
          exists
            sD' : hlist typD tus -> hlist typD tvs -> Prop,
            substD tus tvs s = Some sD' /\
            (forall (us : hlist typD tus)
                    (vs : hlist typD tvs)
                    (vs' : hlist typD tvs'),
               sD us (hlist_app vs vs') <-> sD' us vs).
  Abort.

    Theorem strengthenU_sound
    : forall (s : raw) (n c : nat),
        raw_strengthenU n c s = true ->
        WellFormed_subst s ->
        forall (tus : list typ) (tvs : tenv typ)
               (tus' : list typ)
               (sD : hlist typD (tus ++ tus') ->
                     hlist typD tvs -> Prop),
          substD (tus ++ tus') tvs s = Some sD ->
          n = length tus ->
          c = length tus' ->
          exists
            sD' : hlist typD tus -> hlist typD tvs -> Prop,
            substD tus tvs s = Some sD' /\
            (forall (us : hlist typD tus)
                    (vs : hlist typD tvs)
                    (us' : hlist typD tus'),
               sD (hlist_app us us') vs <-> sD' us vs).
    Abort.

    Theorem forget_sound
    : forall s u s' oe,
        forget u s = (s', oe) ->
        WellFormed_subst s ->
        WellFormed_subst s' /\
        forall tus tvs sD,
          substD tus tvs s = Some sD ->
          exists sD',
            substD tus tvs s' = Some sD' /\
            match oe with
              | None =>
                forall us vs,
                  sD us vs <-> sD' us vs
              | Some e =>
                mentionsU u e = false /\
                match nth_error_get_hlist_nth typD tus u with
                  | Some (existT t get) =>
                    match exprD' tus tvs e t with
                      | None => False
                      | Some eD =>
                        forall us vs,
                          sD us vs <-> (get us = eD us vs /\ sD' us vs)
                    end
                  | None => False
                end
            end.
     Abort.
*)

    Definition raw_substR (tus tvs : tenv typ) (a b : raw) : Prop :=
      Roption (RexprT tus tvs impl) (substD tus tvs b) (substD tus tvs a).

    Theorem set_sound
    : forall (uv : nat) (e : expr) (s s' : raw),
        subst_set uv e s = Some s' ->
        WellFormed_subst s ->
        WellFormed_subst s' /\
        (subst_lookup uv s = None ->
         forall (tus tvs : tenv typ) (t : typ) (val : exprT tus tvs (typD t))
                (get : hlist typD tus -> typD t) (sD : exprT tus tvs Prop),
           substD tus tvs s = Some sD ->
           nth_error_get_hlist_nth typD tus uv =
           Some (existT (fun t0 : typ => hlist typD tus -> typD t0) t get) ->
           exprD' tus tvs e t = Some val ->
           exists sD' : exprT tus tvs Prop,
             substD tus tvs s' = Some sD' /\
             raw_substR tus tvs s s' /\
             (forall (us : hlist typD tus) (vs : hlist typD tvs),
                sD' us vs <-> (sD us vs /\ get us = val us vs))).
    Proof.
      intros. eapply substD_set in H; eauto.
      destruct H. split; auto. intros.
      eapply H1 in H4; eauto.
      destruct H4. exists x.
      forward_reason; split; eauto.
      unfold raw_substR.
      simpl in *.
      Cases.rewrite_all_goal.
      split; eauto.
      { constructor. do 6 red.
        intros. apply equiv_eq_eq in H7; apply equiv_eq_eq in H8; subst.
        eapply H6 in H9. tauto. }
    Qed.

    Instance SubstUpdateOk_subst : SubstUpdateOk SubstUpdate_subst _ :=
    {| substR := raw_substR
     ; set_sound := set_sound
     |}.

    Instance SubstOpen_subst : SubstOpen raw :=
    { subst_drop := raw_drop
    ; subst_weakenU := fun _ x => x
    }.

    Instance SubstOpenOk_subst
    : @SubstOpenOk raw typ expr _ _ _ Subst_subst _ SubstOpen_subst :=
    { drop_sound := substD_drop' }.
    Proof.
      unfold subst_weakenU; simpl.
      intros; subst.
      eapply substD_weaken with (tus' := tus') (tvs' := nil) in H1.
      forward_reason.
      exists (match app_nil_r_trans tvs in _ = X return exprT _ X Prop with
                | eq_refl => x
              end).
      split.
      { transitivity (match app_nil_r_trans tvs in (_ = X)
                            return option (exprT (tus ++ tus') X Prop)
                      with
                        | eq_refl => Some x
                      end).
        { rewrite <- H. clear.
          destruct (app_nil_r_trans tvs). reflexivity. }
        { intros. autorewrite with eq_rw.
          reflexivity. } }
      { intros. autorewrite with eq_rw.
        rewrite <- hlist_app_nil_r. eapply H0. }
    Qed.
  End exprs.
End Make.

Require MirrorCore.Subst.UVarMap.

Module SUBST := Make UVarMap.MAP.
