(** Bounded Instantiated Maps **)
Require Import Coq.Bool.Bool.
Require Import Coq.omega.Omega.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relations.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Prop.
Require Import ExtLib.Data.Pair.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.ListFirstnSkipn.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.VariablesI.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.Subst.FMapSubst.
Require Import MirrorCore.Instantiate.

Require Import MirrorCore.Util.Quant.
Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

(** TODO: This has to be somewhere else **)
Instance Reflexive_pointwise
         {T U} {R : U -> U -> Prop} (Refl : Reflexive R)
: Reflexive (pointwise_relation T R).
Proof.
  red. red. reflexivity.
Qed.

Section parameterized.
  Variable typ : Set.
  Variable expr : Set.

  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Expr_expr : Expr typ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.
  Context {ExprVar_expr : ExprVar expr}.
  Context {ExprVarOk_expr : ExprVarOk _}.
  Context {ExprUVar_expr : ExprUVar expr}.
  Context {ExprUVarOk_expr : ExprUVarOk _}.

  Local Instance RelDec_eq_typ : RelDec (@eq typ) :=
    RelDec_Rty _.
  Local Instance RelDecOk_eq_typ : RelDec_Correct RelDec_eq_typ :=
    @RelDec_Correct_Rty _ _ _.

  Local Existing Instance SUBST.Subst_subst.
  Local Existing Instance SUBST.SubstOk_subst.
  Local Existing Instance SUBST.SubstOpen_subst.
  Local Existing Instance SUBST.SubstOpenOk_subst.

  Definition amap : Type := SUBST.raw expr.
  Definition WellFormed_amap : amap -> Prop := @SUBST.WellFormed _ _ _ _.
  Definition amap_empty : amap := UVarMap.MAP.empty _.
  Definition amap_lookup : nat -> amap -> option expr :=
    @UVarMap.MAP.find _.
  Definition amap_check_set : nat -> expr -> amap -> option amap :=
    @SUBST.raw_set _ _ _ _.
  Definition amap_instantiate (f : nat -> option expr) : amap -> amap :=
    UVarMap.MAP.map (fun e => instantiate f 0 e).
  Definition amap_substD
  : forall (tus tvs : tenv typ), amap -> option (exprT tus tvs Prop) :=
    @SUBST.raw_substD _ _ _ _.
  Definition amap_is_full (* min : uvar *) (len : nat) (m : amap) : bool :=
    UVarMap.MAP.cardinal m ?[ eq ] len.
  Definition amap_domain (m : amap) : list uvar :=
    map fst (UVarMap.MAP.elements m).
  Fixpoint amap_aslist (m : amap) (f n : nat) : list (option expr) :=
    match n with
      | O => nil
      | S n => amap_lookup f m :: amap_aslist m (S f) n
    end.

  Definition Forall_amap (P : uvar -> expr -> Prop) (m : amap) : Prop :=
    forall u e,
      amap_lookup u m = Some e ->
      P u e.

  Lemma Forall_amap_empty
  : forall P, Forall_amap P amap_empty.
  Proof.
    clear. intros.
    red. unfold amap_lookup, amap_empty.
    intros. rewrite FMapSubst.SUBST.FACTS.empty_o in H. congruence.
  Qed.

  Definition bimap_max (maxU maxV : nat) e : Prop :=
    mentionsAny (fun u' => u' ?[ ge ] maxU)
                (fun v' => v' ?[ ge ] maxV) e = false.


  Definition WellFormed_bimap (min : nat) (len : nat) (maxV : nat) (m : amap)
  : Prop :=
    (** 'acyclic' **)
    SUBST.WellFormed m /\
    (** only in this range **)
    Forall_amap (fun k _ => min <= k < min + len) m /\
    (** no forward pointers **)
    Forall_amap (fun k e => bimap_max (min + len) maxV e) m.

  Lemma WellFormed_bimap_empty
  : forall a b c, WellFormed_bimap a b c amap_empty.
  Proof.
    clear - RTypeOk_typ Expr_expr. red.
    intros. refine (conj _ (conj _ _));
            eauto using SUBST.WellFormed_empty, Forall_amap_empty.
    eapply SUBST.WellFormed_empty.
  Qed.

  Lemma WellFormed_bimap_WellFormed_amap
  : forall a b c s,
      WellFormed_bimap a b c s ->
      WellFormed_amap s.
  Proof.
    destruct 1. assumption.
  Qed.

  Lemma amap_instantiates_substD
  : forall tus tvs C (_ : CtxLogic.ExprTApplicative C) f s sD a b c,
      WellFormed_bimap a b c s ->
      amap_substD tus tvs s = Some sD ->
      sem_preserves_if_ho C f ->
      exists sD',
        amap_substD tus tvs (amap_instantiate f s) = Some sD' /\
        C (fun us vs => sD us vs <-> sD' us vs).
  Proof.
    unfold amap_instantiate.
    intros.
    eapply SUBST.raw_substD_instantiate_ho in H2; eauto.
    forward_reason.
    eexists; split; eauto.
    revert H3.
    eapply CtxLogic.exprTAp.
    eapply CtxLogic.exprTPure.
    intros us vs.
    clear. tauto.
  Qed.

  Lemma amap_lookup_substD
  : forall (s : amap) (uv : uvar) (e : expr),
      amap_lookup uv s = Some e ->
      forall (tus tvs : list typ)
             (sD : hlist typD tus -> hlist typD tvs -> Prop),
        amap_substD tus tvs s = Some sD ->
        exists
          (t : typ) (val : exprT tus tvs (typD t))
          (get : hlist typD tus -> typD t),
          nth_error_get_hlist_nth typD tus uv =
          Some (existT (fun t0 : typ => hlist typD tus -> typD t0) t get) /\
          exprD tus tvs t e = Some val /\
          (forall (us : hlist typD tus) (vs : hlist typD tvs),
             sD us vs -> get us = val us vs).
  Proof. eapply SUBST.substD_lookup'; eauto. Qed.

  Lemma amap_substD_amap_empty
    : forall tus tvs,
      exists sD,
        amap_substD tus tvs amap_empty = Some sD /\
        forall a b, sD a b.
  Proof using.
    intros.
    eapply FMapSubst.SUBST.substD_empty.
  Qed.

  Lemma amap_domain_WellFormed
  : forall (s : amap) (ls : list uvar),
       WellFormed_amap s ->
       amap_domain s = ls ->
       forall n : nat, In n ls <-> amap_lookup n s <> None.
  Proof. eapply SUBST.WellFormed_domain. Qed.

  Lemma amap_lookup_normalized
  : forall (s : amap) (e : expr) (u : nat),
      WellFormed_amap s ->
      amap_lookup u s = Some e ->
      forall (u' : nat) (e' : expr),
        amap_lookup u' s = Some e' -> mentionsU u' e = false.
  Proof. eapply SUBST.normalized_fmapsubst. Qed.

  Lemma amap_lookup_amap_instantiate
  : forall u f m,
      amap_lookup u (amap_instantiate f m) =
      match amap_lookup u m with
        | None => None
        | Some e => Some (instantiate f 0 e)
      end.
  Proof.
    unfold amap_lookup, amap_instantiate; intros.
    apply SUBST.FACTS.map_o.
  Qed.

  Lemma syn_check_set
  : forall uv e s s',
      WellFormed_amap s ->
      amap_check_set uv e s = Some s' ->
      let e' := instantiate (fun u => amap_lookup u s) 0 e in
      WellFormed_amap s' /\
      mentionsU uv e'= false /\
      forall u,
        amap_lookup u s' =
        if uv ?[ eq ] u then Some e'
        else
          match amap_lookup u s with
            | None => None
            | Some e =>
              Some (instantiate (fun u =>
                                   if uv ?[ eq ] u then Some e'
                                   else None) 0 e)
          end.
  Proof.
    intros. unfold amap_check_set, SUBST.raw_set in *.
    forward. inv_all; subst.
    split.
    { eapply SUBST.raw_set_WellFormed; eauto.
      instantiate (1 := e). instantiate (1 := uv).
      unfold amap_check_set, SUBST.raw_set in *.
      rewrite H0. reflexivity. }
    split.
    { assumption. }
    intros.
    unfold amap_lookup.
    rewrite SUBST.FACTS.add_o.
    destruct (SUBST.PROPS.F.eq_dec uv u); subst.
    { rewrite rel_dec_eq_true; eauto with typeclass_instances. }
    { rewrite rel_dec_neq_false; eauto with typeclass_instances.
      unfold SUBST.raw_instantiate.
      rewrite SUBST.FACTS.map_o.
      destruct (UVarMap.MAP.find u s); try reflexivity. }
  Qed.

  Lemma mentionsAny_false_mentionsV
    : forall fU fV v e,
      mentionsAny fU fV e = false ->
      mentionsV v e = true ->
      fV v = false.
  Proof.
    intros. eapply mentionsAny_complete_false in H.
    destruct H.
    eauto. eauto.
  Qed.

  Lemma mentionsAny_false_mentionsU
    : forall fU fV u e,
      mentionsAny fU fV e = false ->
      mentionsU u e = true ->
      fU u = false.
  Proof.
    intros. eapply mentionsAny_complete_false in H.
    destruct H.
    eauto. eauto.
  Qed.

  Lemma WellFormed_bimap_check_set
  : forall uv e s min len maxV s',
      amap_check_set uv e s = Some s' ->
      mentionsAny (fun u' => u' ?[ ge ] (min + len))
                  (fun v' => v' ?[ ge ] maxV) e = false ->
      min <= uv < min + len ->
      WellFormed_bimap min len maxV s ->
      WellFormed_bimap min len maxV s'.
  Proof.
    intros.
    eapply syn_check_set in H; eauto.
    red in H2. red.
    { forward_reason.
      split; auto.
      split.
      { red in H3. red.
        intros.
        rewrite H7 in H8.
        consider (uv ?[ eq ] u); intros; subst.
        omega.
        forward. eapply H3; eauto. }
      { red in H4; red; intros.
        rewrite H7 in H8; clear H7.
        consider (uv ?[ eq ] u); intros; subst.
        { inv_all; subst.
          eapply mentionsAny_complete_false; [ eauto | ].
          split; intros.
          { eapply mentionsU_instantiate in H7.
            eapply mentionsAny_complete_false in H0; try eassumption.
            destruct H0.
            destruct H7.
            { eapply H0. tauto. }
            { forward_reason.
              eapply H4 in H7.
              eapply mentionsAny_complete_false in H7; try eassumption.
              destruct H7; eauto. } }
          { eapply mentionsV_instantiate_0 in H7; try eassumption.
            destruct H7.
            { eapply mentionsAny_false_mentionsV in H0; eauto. }
            { destruct H7.
              forward_reason.
              eapply H4 in H8. eapply mentionsAny_false_mentionsV in H8; eauto. } } }
        { forward.
          inv_all; subst.
          eapply mentionsAny_complete_false; try eassumption.
          split.
          { intros.
            eapply H4 in H8.
            eapply mentionsU_instantiate in H9.
            destruct H9.
            { forward_reason; forward.
              eapply mentionsAny_false_mentionsU in H8; eauto. }
            { forward_reason. forward.
              subst. inv_all; subst.
              eapply mentionsU_instantiate in H11.
              destruct H11.
              { forward_reason.
                eapply mentionsAny_false_mentionsU in H11. eapply H11.
                eapply H0. }
              { forward_reason.
                eapply mentionsAny_false_mentionsU in H12. eapply H12.
                eapply H4. eauto. } } }
          { intros.
            eapply mentionsV_instantiate_0 in H9; try eassumption.
            destruct H9.
            { eapply H4 in H8.
              eapply mentionsAny_false_mentionsV in H8; eauto. }
            { forward_reason. forward.
              inv_all; subst.
              eapply mentionsV_instantiate_0 in H11; try eassumption.
              destruct H11.
              { eapply mentionsAny_false_mentionsV in H10. eapply H10.
                eapply H0. }
              { forward_reason.
                eapply H4 in H11.
                eapply mentionsAny_false_mentionsV in H11. eapply H11. auto. } } } } } }
    { destruct H2. assumption. }
  Qed.

  Lemma Forall_amap_instantiate
  : forall (P Q : uvar -> expr -> Prop) f m,
      (forall u e, Q u e -> P u (instantiate f 0 e)) ->
      Forall_amap Q m ->
      Forall_amap P (amap_instantiate f m).
  Proof.
    clear.
    intros. red.
    unfold amap_lookup, amap_instantiate, amap_lookup. intros u e.
    rewrite SUBST.FACTS.map_o.
    consider (UVarMap.MAP.find u m); simpl; intros; try congruence.
    inv_all. eapply H0 in H1. subst; eauto.
  Qed.

  Lemma WellFormed_bimap_instantiate
  : forall s f min len maxV s',
      amap_instantiate f s = s' ->
      (forall u e,
         f u = Some e ->
         mentionsAny (fun u' => u' ?[ ge ] min)
                     (fun v' => v' ?[ ge ] maxV) e = false) ->
      WellFormed_bimap min len maxV s ->
      WellFormed_bimap min len maxV s'.
  Proof.
    red; intros; subst.
    red in H1. forward_reason.
    split.
    { red. intros.
      rewrite SUBST.PROPS.F.find_mapsto_iff in H3.
      unfold amap_instantiate in *.
      rewrite SUBST.FACTS.map_o in H3.
      red. intros.
      consider (UVarMap.MAP.find k s); simpl in *; try congruence.
      intros. inv_all; subst.
      eapply SUBST.PROPS.F.not_find_in_iff.
      rewrite SUBST.FACTS.map_o.
      consider (UVarMap.MAP.find u s); try reflexivity.
      intros. exfalso.
      eapply mentionsU_instantiate in H4.
      destruct H4.
      { destruct H4.
        eapply H. 2: eassumption.
        eapply SUBST.PROPS.F.find_mapsto_iff. eassumption.
        red. eexists.
        eapply SUBST.PROPS.F.find_mapsto_iff. eassumption. }
      { forward_reason.
        specialize (H0 _ _ H4).
        eapply mentionsAny_false_mentionsU in H0; [ | eassumption ].
        eapply H1 in H5. consider (u ?[ ge ] min).
        { congruence. }
        { intros. omega. } } }
    split.
    { revert H1. eapply Forall_amap_instantiate. trivial. }
    { revert H2. eapply Forall_amap_instantiate; intros.
      unfold bimap_max in *.
      eapply mentionsAny_complete_false; [ eauto | ].
      eapply mentionsAny_complete_false in H2; [ | eauto ].
      forward_reason; split.
      { intros.
        eapply mentionsU_instantiate in H4.
        destruct H4; forward_reason.
        { eauto. }
        { eapply H0 in H4.
          eapply mentionsAny_false_mentionsU in H4. 2: eassumption.
          clear - H4.
          consider (u0 ?[ ge ] (min + len)); auto.
          intros. rewrite rel_dec_eq_true in H4; eauto with typeclass_instances.
          omega. } }
      { intros.
        eapply mentionsV_instantiate_0 in H4; try eassumption.
        destruct H4.
        eauto.
        forward_reason. eapply H0 in H5.
        eapply mentionsAny_false_mentionsV in H5. 2: eauto. eauto. } }
  Qed.

  Definition nothing_in_range a b m : Prop :=
    forall u, u < b -> amap_lookup (a + u) m = None.
  Definition only_in_range min len m :=
    Forall_amap (fun k _ => min <= k < min + len) m.

  Lemma only_in_range_0_empty
  : forall a am,
      only_in_range a 0 am ->
      UVarMap.MAP.Equal am amap_empty.
  Proof.
    clear. unfold Forall_amap. red.
    intros.
    specialize (H y). unfold amap_lookup in *.
    rewrite SUBST.FACTS.empty_o.
    destruct (UVarMap.MAP.find y am); auto.
    exfalso. specialize (H _ eq_refl). omega.
  Qed.

  Lemma Forall_amap_Proper
  : Proper (pointwise_relation _ (pointwise_relation _ iff) ==> UVarMap.MAP.Equal ==> iff)
           Forall_amap.
  Proof.
    do 3 red; intros.
    split; intros; red; intros;
    eapply SUBST.FACTS.find_mapsto_iff in H2;
    eapply SUBST.FACTS.Equal_mapsto_iff in H0; eauto.
    - eapply H0 in H2.
      eapply H1 in H2.
      eapply H; eauto.
    - eapply H0 in H2.
      eapply H1 in H2.
      eapply H; eauto.
  Qed.

  Lemma only_in_range_0_WellFormed_pre_entry
  : forall a am mV,
      only_in_range a 0 am ->
      WellFormed_bimap a 0 mV am.
  Proof.
    clear. unfold WellFormed_bimap.
    intros. eapply only_in_range_0_empty in H.
    split.
    - red. intros.
      eapply SUBST.FACTS.Equal_mapsto_iff in H.
      eapply H in H0. clear - H0.
      eapply SUBST.FACTS.empty_mapsto_iff in H0.
      destruct H0.
    - split.
      + eapply Forall_amap_Proper; eauto.
        eapply Reflexive_pointwise.
        eapply Reflexive_pointwise. eauto with typeclass_instances.
        eapply Forall_amap_empty.
      + eapply Forall_amap_Proper; eauto.
        eapply Reflexive_pointwise.
        eapply Reflexive_pointwise. eauto with typeclass_instances.
        eapply Forall_amap_empty.
  Qed.

  (** Start pigeonhole stuff **)
  Lemma cardinal_remove
  : forall m x y,
      amap_lookup x m = Some y ->
      UVarMap.MAP.cardinal m = S (UVarMap.MAP.cardinal (UVarMap.MAP.remove x m)).
  Proof.
    clear. intros.
    do 2 rewrite SUBST.PROPS.cardinal_fold.
    assert (UVarMap.MAP.Equal m (UVarMap.MAP.add x y (UVarMap.MAP.remove x m))).
    { red. intros.
      rewrite SUBST.PROPS.F.add_o.
      rewrite SUBST.PROPS.F.remove_o.
      destruct (SUBST.PROPS.F.eq_dec x y0). subst; auto.
      auto. }
    etransitivity.
    (rewrite SUBST.PROPS.fold_Equal with (eqA := @eq nat); try eassumption); eauto.
    compute; intros; subst; auto.
    compute; intros; subst; auto.
    rewrite <- plus_n_O.
    rewrite SUBST.PROPS.fold_add. reflexivity.
    eauto.
    compute; intros; subst; auto.
    compute; intros; subst; auto.
    eapply UVarMap.MAP.remove_1. reflexivity.
  Qed.

  Lemma cardinal_not_remove
  : forall m x,
      amap_lookup x m = None ->
      UVarMap.MAP.cardinal m = UVarMap.MAP.cardinal (UVarMap.MAP.remove x m).
  Proof.
    clear. intros.
    assert (UVarMap.MAP.Equal m (UVarMap.MAP.remove x m)).
    { red. intros.
      rewrite SUBST.PROPS.F.remove_o.
      destruct (SUBST.PROPS.F.eq_dec x y). subst; auto.
      auto. }
    rewrite <- H0. reflexivity.
  Qed.

  Lemma subst_pull_sound
  : forall b a m m',
      subst_pull a b m = Some m' ->
      nothing_in_range a b m' /\
      UVarMap.MAP.cardinal m' = UVarMap.MAP.cardinal m - b /\
      (forall u, u < a \/ u >= a + b -> amap_lookup u m = amap_lookup u m') /\
      (forall u, u < b -> amap_lookup (a + u) m <> None).
  Proof.
    clear.
    induction b.
    { simpl. intros. inv_all; subst.
      split.
      { red. intros; exfalso; omega. }
      split.
      { omega. }
      split.
      { auto. }
      { intros. exfalso; omega. } }
    { simpl. unfold SUBST.raw_drop.
      intros. forwardy.
      eapply IHb in H. forward_reason.
      inv_all. subst.
      split.
      { red. intros.
        unfold amap_lookup. rewrite SUBST.PROPS.F.remove_o.
        destruct (SUBST.PROPS.F.eq_dec a (a + u)); auto.
        destruct u.
        { exfalso; omega. }
        { replace (a + S u) with (S a + u) by omega.
          red in H. eapply H. omega. } }
      split.
      { replace (UVarMap.MAP.cardinal m - S b) with
        ((UVarMap.MAP.cardinal m - b) - 1) by omega.
        rewrite <- H2. clear - H0.
        rewrite (@cardinal_remove _ _ _ H0). omega. }
      split.
      { intros.
        destruct H1.
        + rewrite H3; [ | left; eauto ].
          unfold amap_lookup.
          rewrite SUBST.PROPS.F.remove_neq_o; auto.
        + rewrite H3; [ | right; omega ].
          unfold amap_lookup.
          rewrite SUBST.PROPS.F.remove_neq_o; auto.
          omega. }
      { intros.
        destruct u.
        { rewrite H3; [ | left; omega ].
          replace (a + 0) with a. change_rewrite H0. congruence.
          clear. apply plus_n_O. }
        { replace (a + S u) with (S a + u) by omega.
          apply H4. omega. } } }
  Qed.

  Lemma subst_pull_complete
  : forall b a m,
      (forall u, u < b -> amap_lookup (a + u) m <> None) ->
      exists m',
        subst_pull a b m = Some m'.
  Proof.
    clear. induction b; simpl; intros; eauto.
    { destruct (IHb (S a) m); clear IHb.
      { intros. replace (S a + u) with (a + S u) by omega.
        eapply H. omega. }
      { rewrite H0.
        eapply subst_pull_sound in H0.
        forward_reason. unfold SUBST.raw_drop.
        rewrite <- H2 by (left; omega).
        specialize (H 0).
        replace (a + 0) with a in H by omega.
        destruct (amap_lookup a m); eauto.
        exfalso. eapply H; auto. omega. } }
  Qed.

  Fixpoint test_range from len m :=
    match len with
      | 0 => true
      | S len =>
        match amap_lookup from m with
          | None => false
          | Some _ => test_range (S from) len (UVarMap.MAP.remove from m)
        end
    end.

  Lemma test_range_true_all
  : forall l f m,
      test_range f l m = true ->
      forall u, u < l -> amap_lookup (f + u) m <> None.
  Proof.
    clear. induction l.
    { intros; exfalso; omega. }
    { simpl; intros; forward.
      specialize (IHl _ _ H1).
      destruct u.
      { replace (f + 0) with f by omega. congruence. }
      { replace (f + S u) with (S f + u) by omega.
        cutrewrite (amap_lookup (S f + u) m =
                    amap_lookup (S f + u) (UVarMap.MAP.remove f m)).
        { apply IHl. omega. }
        unfold amap_lookup.
        rewrite SUBST.PROPS.F.remove_neq_o; auto. omega. } }
  Qed.

  Lemma cardinal_le_range
  : forall len min m,
      only_in_range min len m ->
      UVarMap.MAP.cardinal m <= len.
  Proof.
    clear.
    induction len.
    { intros.
      eapply only_in_range_0_empty in H.
      cut (UVarMap.MAP.cardinal m = 0); try omega.
      apply SUBST.PROPS.cardinal_1.
      rewrite H.
      apply UVarMap.MAP.empty_1. }
    { intros.
      assert (only_in_range min len (UVarMap.MAP.remove (min + len) m)).
      { red. red in H. red. intros.
        unfold amap_lookup in H0.
        rewrite SUBST.PROPS.F.remove_o in H0.
        destruct (SUBST.PROPS.F.eq_dec (min + len) u); try congruence.
        eapply H in H0. omega. }
      { eapply IHlen in H0.
        consider (UVarMap.MAP.find (min + len) m); intros.
        { erewrite cardinal_remove; eauto.
          omega. }
        { erewrite cardinal_not_remove; eauto. } } }
  Qed.

  Lemma subst_getInstantiation
  : forall tus tvs ts m maxV P,
      WellFormed_bimap (length tus) (length ts) maxV m ->
      amap_substD (tus ++ ts) tvs m = Some P ->
      amap_is_full (length ts) m = true ->
      exists x : hlist (fun t => exprT tus tvs (typD t)) ts,
        forall us vs,
          let us' :=
              hlist_map (fun t (x : exprT tus tvs (typD t)) => x us vs) x
          in
          P (HList.hlist_app us us') vs.
  Proof.
    intros.
    assert (exists m',
              subst_pull (length tus) (length ts) m = Some m' /\
              UVarMap.MAP.Empty m').
    { unfold amap_is_full in H1.
      consider (UVarMap.MAP.cardinal m ?[ eq ] length ts); intros.
      assert (only_in_range (length tus) (length ts) m).
      { clear - H. red in H. red; intros.
        tauto. }
      clear - H1 H2.
      destruct (@subst_pull_complete (length ts) (length tus) m).
      { eapply test_range_true_all.
        generalize dependent (length tus).
        generalize dependent m.
        induction (length ts); intros.
        { reflexivity. }
        { simpl.
          consider (amap_lookup n0 m).
          { intros.
            eapply IHn.
            - erewrite cardinal_remove in H1; eauto.
            - red. intros. red. intros.
              unfold amap_lookup in H0.
              rewrite SUBST.PROPS.F.remove_o in H0.
              destruct (SUBST.PROPS.F.eq_dec n0 u); try congruence.
              eapply H2 in H0. omega. }
          { intros. exfalso.
            assert (only_in_range (S n0) n m).
            { red. red; intros. red in H2.
              consider (n0 ?[ eq ] u); intros; subst; try congruence.
              eapply H2 in H0. omega. }
            eapply cardinal_le_range in H0. omega. } }  }
      rewrite H. eexists; split; eauto.
      eapply subst_pull_sound in H.
      assert (only_in_range (length tus) 0 x).
      { forward_reason.
        red. red. intros.
        exfalso.
        assert ((u < length tus \/ u >= length tus + length ts) \/
                (exists u', u' < length ts /\ u = length tus + u')).
        { consider (u ?[ lt ] length tus); try auto; intros.
          consider (u ?[ ge ] (length tus + length ts)); try auto; intros.
          right. exists (u - length tus). split; try omega. }
        destruct H6.
        { rewrite <- H3 in H5; eauto.
          eapply H2 in H5. omega. }
        { forward_reason. subst.
          red in H.
          rewrite H in H5. congruence. auto. } }
      { eapply  only_in_range_0_empty in H0.
        rewrite H0.
        eapply UVarMap.MAP.empty_1. } }
    { forward_reason.
      eapply pull_sound in H2; eauto using SUBST.SubstOpenOk_subst.
      { forward_reason.
        specialize (@H4 tus ts tvs _ eq_refl eq_refl H0).
        forward_reason.
        exists x2. simpl. intros.
        eapply H9.
        assert (UVarMap.MAP.Equal x (UVarMap.MAP.empty expr)).
        { red. red in H3. intros.
          rewrite SUBST.FACTS.empty_o.
          eapply SUBST.FACTS.not_find_in_iff.
          red. intro. destruct H10. eapply H3.
          eauto. }
        generalize (@SUBST.raw_substD_Equal typ _ _ _ tus tvs x (UVarMap.MAP.empty _) _ H7 H10).
        destruct (SUBST.substD_empty tus tvs).
        intros.
        forward_reason.
        eapply H13; clear H13.
        change_rewrite H12 in H11. inv_all; subst. eauto. }
      { eapply WellFormed_bimap_WellFormed_amap; eauto. } }
  Qed.

  Lemma only_in_range_empty : forall a b,
      only_in_range a b amap_empty.
  Proof.
    clear. red. intros.
    eapply Forall_amap_empty.
  Qed.

  Lemma WellFormed_amap_amap_empty : WellFormed_amap amap_empty.
  Proof. red. eapply FMapSubst.SUBST.WellFormed_empty. Qed.

  Lemma list_substD_app
  : forall tus tvs l2 l1 from sD,
      FMapSubst.SUBST.list_substD tus tvs from (l1 ++ l2) = Some sD ->
      exists s1D s2D,
        FMapSubst.SUBST.list_substD tus tvs from l1 = Some s1D /\
        FMapSubst.SUBST.list_substD tus tvs (from + length l1) l2 = Some s2D /\
        forall us vs,
          sD us vs <-> (s1D us vs /\ s2D us vs).
  Proof.
    induction l1; simpl; intros.
    { rewrite <- plus_n_O.
      do 2 eexists; split; eauto. split; eauto.
      intuition. }
    { destruct a; forward; inv_all.
      { eapply IHl1 in H2; forward_reason.
        Cases.rewrite_all_goal.
        do 2 eexists; split; eauto.
        simpl. split.
        rewrite <- Plus.plus_Snm_nSm. eassumption.
        subst; intros. rewrite H5. intuition. }
      { eapply IHl1 in H; forward_reason.
        rewrite <- Plus.plus_Snm_nSm.
        eauto. } }
  Qed.

  Lemma amap_substD_list_substD
  : forall tus tvs am (from len : nat) sD maxV,
      WellFormed_bimap from len maxV am ->
      amap_substD tus tvs am = Some sD ->
      exists sD',
        FMapSubst.SUBST.list_substD tus tvs from (amap_aslist am from len) = Some sD' /\
        forall us vs,
          sD us vs <-> sD' us vs.
  Proof.
    destruct 1.
    intros; eapply FMapSubst.SUBST.amap_substD_list_substD; eauto.
    destruct H0. eauto.
  Qed.

  Lemma amap_aslist_app
    : forall a y x z,
      amap_aslist a x (y + z) =
      amap_aslist a x y ++ amap_aslist a (x + y) z.
  Proof.
    induction y; simpl.
    { intros. f_equal. omega. }
    { intros. f_equal. rewrite IHy. f_equal. f_equal. omega. }
  Qed.

  Lemma amap_aslist_nth_error
    : forall ln st (mp : amap) n,
      nth_error (amap_aslist mp st ln) n =
      if n ?[ lt ] ln then Some (amap_lookup (st + n) mp) else None.
  Proof.
    clear.
    induction ln; simpl; intros; destruct n; auto.
    - simpl. unfold value. f_equal. f_equal. omega.
    - simpl nth_error. rewrite IHln.
      consider (n ?[ lt ] ln);
        consider (S n ?[ lt ] S ln);
        auto; try solve [ intros; exfalso; omega ].
      intros.
      f_equal. f_equal. omega.
  Qed.

  Lemma pigeon_principle'
  : forall n (m : amap) low,
      UVarMap.MAP.cardinal m > n ->
      Forall_amap (fun k _ => low <= k < low + n) m ->
      False.
  Proof using.
    induction n.
    { simpl. intros.
      assert (exists x, UVarMap.MAP.cardinal m = S x).
      { destruct (UVarMap.MAP.cardinal m); eauto.
        exfalso; omega. }
      destruct H1.
      eapply FMapSubst.SUBST.PROPS.cardinal_inv_2 in H1.
      destruct H1.
      eapply FMapSubst.SUBST.FACTS.find_mapsto_iff in m0.
      eapply H0 in m0.
      omega. }
    { intros.
      consider (UVarMap.MAP.find low m).
      { intros.
        specialize (IHn (UVarMap.MAP.remove low m) (S low)).
        apply IHn; clear IHn.
        { erewrite cardinal_remove in H; [ | eassumption ].
          eapply gt_S_n in H. assumption. }
        { red. red in H0.
          intros.
          unfold amap_lookup in *.
          rewrite FMapSubst.SUBST.PROPS.F.remove_o in H2.
          destruct (UVarMap.MAP.E.eq_dec low u); try congruence.
          eapply H0 in H2. omega. } }
      { intros.
        eapply IHn with (m:=m) (low :=S low).
        { omega. }
        { clear - H0 H1.
          unfold Forall_amap in *.
          intros.
          assert (u <> low).
          { unfold amap_lookup in H.
            intro. subst.
            rewrite H1 in H. congruence. }
          { eapply H0 in H.
            omega. } } } }
  Qed.

  Lemma pigeon_principle
  : forall (m : amap) n low,
      amap_is_full n m = true ->
      Forall_amap (fun k _ => low <= k < low + n) m ->
      forall k, k < n ->
                amap_lookup (low + k) m <> None.
  Proof using.
    unfold amap_is_full.
    intros m n low H.
    rewrite rel_dec_correct in H.
    red; intros. revert H2. revert H0. revert H.
    revert low. revert m. generalize dependent n. induction k.
    { intros.
      destruct n; try omega.
      eapply pigeon_principle' with (m:=m) (n:=n) (low:=S low).
      { omega. }
      { red. intros.
        assert (low <> u).
        { intro. subst. replace (u + 0) with u in H2 by omega. congruence. }
        eapply H0 in H3. omega. } }
    { intros.
      destruct n; try omega.
      eapply lt_S_n in H1.
      consider (amap_lookup low m).
      { intros.
        unfold amap_lookup in *.
        eapply (IHk _ H1 (UVarMap.MAP.remove low m) (S low)).
        { erewrite cardinal_remove in H by eassumption.
          omega. }
        { clear - H0.
          unfold Forall_amap in *. intros.
          unfold amap_lookup in H.
          rewrite FMapSubst.SUBST.FACTS.remove_o in H.
          destruct (UVarMap.MAP.E.eq_dec low u); try congruence.
          eapply H0 in H. omega. }
        { rewrite FMapSubst.SUBST.FACTS.remove_o.
          destruct (UVarMap.MAP.E.eq_dec low (S low + k)); auto.
          rewrite <- H2. f_equal. omega. } }
      { intros.
        apply (@pigeon_principle' n m (S low)).
        { omega. }
        { unfold Forall_amap in *; intros.
          assert (u <> low) by congruence.
          eapply H0 in H4.
          omega. } } }
  Qed.

End parameterized.
