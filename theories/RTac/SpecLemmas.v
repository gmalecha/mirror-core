Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relations.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Prop.
Require Import ExtLib.Data.Pair.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.CoreK.

Require Import MirrorCore.Util.Quant.
Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section spec_lemmas.
  Context {typ : Type}.
  Context {expr : Type}.

  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.
  Context {ExprUVar_expr : ExprUVar expr}.
  Context {ExprUVarOk_expr : ExprUVarOk ExprUVar_expr}.

  Local Hint Constructors WellFormed_ctx_subst.
  Lemma WellFormed_ctx_subst_fromAll
  : forall t (c : Ctx typ expr) (cs : ctx_subst (CAll c t)),
      WellFormed_ctx_subst cs ->
      WellFormed_ctx_subst (fromAll cs).
  Proof.
    intros.
    refine match H in @WellFormed_ctx_subst _ _ _ C S
                 return match C as C return ctx_subst C -> Prop with
                          | CAll _ _ => fun x => WellFormed_ctx_subst (fromAll x)
                          | _ => fun _ => True
                        end S
           with
             | WF_AllSubst _ _ _ pf => pf
             | _ => I
           end.
  Qed.

  Lemma WellFormed_ctx_subst_fromHyp
  : forall t (c : Ctx typ expr) (cs : ctx_subst (CHyp c t)),
      WellFormed_ctx_subst cs ->
      WellFormed_ctx_subst (fromHyp cs).
  Proof.
    intros.
    refine match H in @WellFormed_ctx_subst _ _ _ C S
                 return match C as C return ctx_subst C -> Prop with
                          | CHyp _ _ => fun x => WellFormed_ctx_subst (fromHyp x)
                          | _ => fun _ => True
                        end S
           with
             | WF_HypSubst _ _ _ pf => pf
             | _ => I
           end.
  Qed.
  Local Hint Resolve WellFormed_ctx_subst_fromAll WellFormed_ctx_subst_fromHyp.

  Lemma pctxD_remembers {c s l a sD pD}
  : forall (WFp : WellFormed_bimap (length (getUVars c)) (length l) a),
      WellFormed_ctx_subst s ->
    pctxD s = Some sD ->
    amap_substD (getUVars c ++ l) (getVars c) a = Some pD ->
    exists sD',
      pctxD (remembers s l a) = Some sD' /\
      forall us vs (P : exprT _ _ Prop),
        (sD (fun us vs =>
               forall us', pD (hlist_app us us') vs -> P (hlist_app us us') vs) us vs <->
         sD' P us vs).
  Proof.
    simpl. intros.
    rewrite H0.
    destruct (pctxD_substD H H0) as [ ? [ ? ? ] ].
    eapply amap_instantiates_substD
      with (f := fun u => ctx_lookup u s)
           (C := fun (P : exprT (getUVars c ++ l) (getVars c) Prop) =>
                   forall us vs, sD (fun us vs => x us vs -> forall us', P (hlist_app us us') vs) us vs)
           in H1.
    forward_reason.
    rewrite H1.
    eexists; split; eauto.
    simpl. intros.
    split.
    { eapply Ap_pctxD; eauto.
      generalize (H3 us vs); clear H3.
      eapply Ap_pctxD; eauto.
      generalize (H4 us vs); clear H4.
      eapply Ap_pctxD; eauto.
      eapply Pure_pctxD; eauto.
      intros.
      eapply _forall_sem; intros.
      eapply H5; clear H5.
      eapply H3; eauto. }
    { eapply Ap_pctxD; eauto.
      generalize (H3 us vs); clear H3.
      eapply Ap_pctxD; eauto.
      generalize (H4 us vs); clear H4.
      eapply Ap_pctxD; eauto.
      eapply Pure_pctxD; eauto.
      intros.
      eapply _forall_sem with (x := us') in H5; intros.
      eapply H5; clear H5.
      eapply H3; eauto. }
    { eauto. }
    { clear - H0. constructor.
      { intros. eapply Pure_pctxD; eauto. }
      { intros. generalize (H1 us vs).
        eapply Ap_pctxD; eauto.
        generalize (H us vs).
        eapply Ap_pctxD; eauto.
        eapply Pure_pctxD; eauto. } }
    { eassumption. }
    { red. intros.
      destruct (pctxD_substD H H0) as [ ? [ ? ? ] ].
      eapply ctx_substD_lookup in H4; eauto.
      forward_reason.
      eapply exprD'_weakenU with (tus' := l) in H8; eauto.
      destruct H8 as [ ? [ ? ? ] ].
      eapply nth_error_get_hlist_nth_weaken in H4.
      revert H4. instantiate (1 := l).
      simpl. destruct 1 as [ ? [ ? ? ] ].
      rewrite H5 in H4. inv_all. subst.
      eexists; split; eauto.
      intros us vs.
      generalize (H7 us vs); clear H7.
      eapply Ap_pctxD; eauto.
      eapply Pure_pctxD; eauto. intros.
      rewrite <- H11; clear H11; eauto.
      rewrite <- H10; clear H10.
      eauto. }
  Qed.

  Lemma _exists_impl : forall l (P Q : hlist typD l -> Prop),
                         (forall x, P x -> Q x) ->
                         _exists _ l P -> _exists _ l Q.
  Proof.
    clear. intros.
    eapply _exists_sem in H0. eapply _exists_sem.
    destruct H0. exists x. auto.
  Qed.

  Lemma Ap_impls : forall (Ps : list Prop) (P Q : Prop),
                     _impls Ps (P -> Q) ->
                     _impls Ps P -> _impls Ps Q.
  Proof.
    clear. induction Ps; simpl; eauto.
  Qed.

  Opaque remembers.

  Lemma GoalImplies_GConj_
  : forall c (cs : ctx_subst c) l r,
      GoalImplies (cs, GConj l r) (cs, GConj_ l r).
  Proof.
    simpl; intros.
    split; auto.
    split.
    { destruct l; destruct r; inversion H; try constructor; eauto;
      try constructor. }
    { forward.
      assert (   (l = GSolved /\ r = GConj l r)
                 \/ (r = GSolved /\ l = GConj l r)
                 \/ (GConj_ l r = GConj l r)).
      { clear. destruct l; destruct r; simpl;
               try solve [ left; eauto | right; left; eauto | right; right; congruence ]. }
      destruct H3 as [ ? | [ ? | ? ] ]; forward_reason.
      { subst l. destruct H4. simpl.
        rewrite H2.
        split; [ reflexivity | ].
        intros.
        eapply Pure_pctxD; eauto. intros; tauto. }
      { destruct H4; subst. simpl.
        rewrite H2.
        split; [ reflexivity | ].
        intros.
        eapply Pure_pctxD; eauto. intros; tauto. }
      { destruct H3.
        simpl in *. forward.
        split; [ reflexivity | ].
        inv_all; subst.
        intros.
        eapply Pure_pctxD; eauto. } }
  Qed.

  Lemma GoalImplies_GConj
  : forall c (cs : ctx_subst c) l r,
      GoalImplies (cs, GConj_ l r) (cs, GConj l r).
  Proof.
    simpl; intros.
    split; auto.
    split.
    { inversion H; subst.
      destruct l; destruct r; simpl; auto; try constructor; auto. }
    { forward.
      assert (   (l = GSolved /\ r = GConj l r)
                 \/ (r = GSolved /\ l = GConj l r)
                 \/ (GConj_ l r = GConj l r)).
      { clear. destruct l; destruct r; simpl;
               try solve [ left; eauto | right; left; eauto | right; right; congruence ]. }
      destruct H5 as [ ? | [ ? | ? ] ]; forward_reason.
      { subst l. destruct H6. simpl.
        rewrite H3.
        split; [ reflexivity | ].
        intros.
        eapply Pure_pctxD; eauto. inv_all; subst. intros; tauto. }
      { destruct H6; subst. simpl.
        rewrite H2.
        split; [ reflexivity | ].
        intros.
        eapply Pure_pctxD; eauto. inv_all; subst. intros; tauto. }
      { destruct H5.
        simpl in *. forward.
        split; [ reflexivity | ].
        inv_all; subst.
        intros.
        eapply Pure_pctxD; eauto. } }
  Qed.

  Lemma rtac_spec_All_More
    : forall ctx s t g c g',
      rtac_spec (AllSubst (t:=t) s) g (More_ c g') ->
      rtac_spec (ctx:=ctx) s (GAll t g) (More_ (fromAll c) (GAll t g')).
  Proof.
    clear. unfold rtac_spec; simpl; intros.
    inv_all. forward_reason.
    forward_reason.
    rewrite (ctx_subst_eta c) in *.
    simpl in *; inv_all; subst.
    split; auto. split; auto.
    { constructor. auto. }
    forward. inv_all; subst.
    destruct H7. inv_all. subst.
    split; auto.
    intros. gather_facts.
    eapply Pure_pctxD; eauto.
  Qed.

  Lemma rtac_spec_All_Solved
    : forall ctx s t g c,
      rtac_spec (AllSubst (t:=t) s) g (Solved c) ->
      rtac_spec (ctx:=ctx) s (GAll t g) (Solved (fromAll c)).
  Proof.
    clear - RTypeOk_typ. intros.
    eapply Proper_rtac_spec.
    3: eapply rtac_spec_All_More.
    - reflexivity.
    - change (Solved (fromAll c)) with (More (fromAll c) GSolved).
      eapply More_More_.
      instantiate (1 := GSolved).
      red. split.
      { split; constructor. constructor. }
      { simpl.
        constructor. constructor; auto. }
    - eapply Proper_rtac_spec.
      + reflexivity.
      + symmetry. eapply More_More_. reflexivity.
      + apply H.
  Qed.

  Lemma rtac_spec_GConj_Solved
    : forall ctx c s g1 g2 r,
      rtac_spec s g1 (Solved (c:=ctx) c) ->
      rtac_spec c g2 r ->
      rtac_spec s (GConj_ g1 g2) r.
  Proof.
    unfold rtac_spec. intros.
    destruct r; auto;
    intros; inv_all; forward_reason.
    { split; auto.
      split; auto.
      simpl.
      forward.
      forward_reason.
      split.
      { etransitivity; eauto. }
      intros. gather_facts.
      eapply pctxD_SubstMorphism; eauto.
      gather_facts.
      eapply Pure_pctxD; eauto. }
    { split; auto.
      simpl. forward; forward_reason.
      split.
      { etransitivity; eauto. }
      intros. gather_facts.
      eapply pctxD_SubstMorphism; eauto.
      gather_facts.
      eapply Pure_pctxD; eauto. }
  Qed.
  Lemma rtac_spec_GConj_More_
    : forall ctx c s g1 g2 r g,
      rtac_spec s g1 (More_ (c:=ctx) c g) ->
      rtac_spec c g2 r ->
      rtac_spec c (GConj_ g g2) r ->
      rtac_spec s (GConj_ g1 g2) r.
  Proof.
    unfold rtac_spec. intros.
    destruct r; auto;
    intros; inv_all; forward_reason.
    { split; auto.
      split; auto.
      simpl.
      destruct H1; auto.
      { constructor; eauto. }
      simpl in H9. destruct H9.
      forward.
      forward_reason.
      split.
      { etransitivity; eauto. }
      intros. gather_facts.
      eapply pctxD_SubstMorphism; eauto.
      gather_facts.
      eapply Pure_pctxD; eauto.
      tauto. }
    { split; auto.
      simpl.
      destruct H1; eauto.
      { constructor; auto. }
      simpl in *.
      forward; forward_reason.
      split.
      { etransitivity; eauto. }
      intros. gather_facts.
      eapply pctxD_SubstMorphism; eauto.
      gather_facts.
      eapply Pure_pctxD; eauto. tauto. }
  Qed.

  Lemma rtac_spec_Hyp_Solved
    : forall e (ctx : Ctx typ expr) (s : ctx_subst ctx)
             (c : ctx_subst (CHyp ctx e)) (g : Goal typ expr),
      rtac_spec (HypSubst s) g (Solved c) ->
      rtac_spec s (GHyp e g) (Solved (fromHyp c)).
  Proof.
    clear. simpl. intros.
    inv_all. destruct H; auto.
    split; auto.
    forward.
    destruct H6. inv_all; subst.
    simpl in *.
    forward. inv_all. subst.
    split; auto.
  Qed.

  Lemma rtac_spec_Hyp_More
    : forall (g0 g : Goal typ expr) (e : expr) (ctx : Ctx typ expr)
             (s : ctx_subst ctx) (c : ctx_subst (CHyp ctx e)),
      rtac_spec (HypSubst s) g (More_ c g0) ->
      rtac_spec s (GHyp e g) (More_ (fromHyp c) (GHyp e g0)).
  Proof.
    simpl. intros. inv_all.
    forward_reason.
    split; auto.
    split.
    { constructor. auto. }
    forward. forward_reason.
    inv_all. subst.
    simpl in *. forward. inv_all; subst.
    split; auto.
    intros. gather_facts.
    eapply Pure_pctxD; eauto.
  Qed.

  Lemma rtac_spec_Conj_Solved
    : forall ctx s g1 g2 c r,
      rtac_spec s g1 (Solved c) ->
      rtac_spec c g2 r ->
      rtac_spec (ctx:=ctx) s (GConj_ g1 g2) r.
  Proof.
    clear. simpl.
    destruct r; simpl; auto; intros; inv_all; forward_reason.
    { split; auto. split; auto.
      forward. forward_reason.
      split.
      { etransitivity; eauto. }
      { intros; gather_facts.
        eapply pctxD_SubstMorphism; eauto.
        gather_facts.
        eapply Pure_pctxD; eauto. } }
    { split; auto.
      forward. forward_reason.
      split.
      { etransitivity; eauto. }
      { intros; gather_facts.
        eapply pctxD_SubstMorphism; eauto.
        gather_facts.
        eapply Pure_pctxD; eauto. } }
  Qed.

  Lemma rtac_spec_GConj_More_Solved
    : forall ctx s s' s'' g1 g2 g1',
      rtac_spec s g1 (More_ s' g1') ->
      rtac_spec s' g2 (Solved s'') ->
      rtac_spec (ctx:=ctx) s (GConj_ g1 g2) (More_ s'' g1').
  Proof.
    clear. simpl.
    intros; inv_all. forward_reason.
    split; auto. split; auto.
    forward. forward_reason.
    split.
    { etransitivity; eauto. }
    intros; gather_facts.
    eapply pctxD_SubstMorphism; eauto.
    gather_facts.
    eapply Pure_pctxD; eauto.
  Qed.

  Lemma rtac_spec_GConj_More_More
    : forall ctx s s' s'' g1 g2 g1' g2',
      rtac_spec s g1 (More_ s' g1') ->
      rtac_spec s' g2 (More_ s'' g2') ->
      rtac_spec (ctx:=ctx) s (GConj_ g1 g2) (More_ s'' (GConj_ g1' g2')).
  Proof.
    clear. simpl.
    intros; inv_all. forward_reason.
    split; auto.
    split.
    { constructor; auto. }
    forward. forward_reason.
    split.
    { etransitivity; eauto. }
    intros; gather_facts.
    eapply pctxD_SubstMorphism; eauto.
    gather_facts.
    eapply Pure_pctxD; eauto.
    tauto.
  Qed.

  Lemma rtac_spec_GSolved_Solved
    : forall ctx s, rtac_spec (ctx:=ctx) s GSolved (Solved s).
  Proof.
    clear. simpl.
    intros. split; auto.
    forward. split. reflexivity.
    eapply Pure_pctxD; eauto.
  Qed.

  Lemma ExprTApplicative_with_extra
    : forall (l : list typ) (ctx : Ctx typ expr) (s : ctx_subst ctx)
             (e : exprT (getUVars ctx) (getVars ctx) Prop ->
                  exprT (getAmbientUVars ctx) (getAmbientVars ctx) Prop),
      pctxD s = Some e ->
      CtxLogic.ExprTApplicative
        (fun P : exprT (getUVars ctx ++ l) (getVars ctx) Prop =>
           forall (us : hlist typD (getAmbientUVars ctx))
                  (vs : hlist typD (getAmbientVars ctx)),
             e
               (fun (us0 : hlist typD (getUVars ctx))
                    (vs0 : hlist typD (getVars ctx)) =>
                  forall z : hlist typD l, P (hlist_app us0 z) vs0) us vs).
  Proof.
    clear.
    constructor.
    { intros. eapply Pure_pctxD; eauto. }
    { intros. gather_facts. eapply Pure_pctxD; eauto. }
  Qed.

  Lemma rtac_spec_remembers_full_Solved
    : forall (l : list typ)
             (a : amap expr)
             (g : Goal typ expr)
             (ctx : Ctx typ expr)
             (s : ctx_subst ctx)
             (c : ctx_subst (CExs ctx l)),
      amap_is_full (length l) (fst (fromExs c)) = true ->
      rtac_spec (remembers s l a) g (Solved c) ->
      rtac_spec s (GExs l a g) (Solved (snd (fromExs c))).
  Proof.
    unfold rtac_spec. simpl.
    intros. inv_all.
    Transparent remembers. unfold remembers in *. Opaque remembers.
    forward_reason.
    assert (WellFormed_ctx_subst
              (ExsSubst (ts:=l) s (amap_instantiate (fun u : nat => ctx_lookup u s) a))).
    { edestruct remembers_sound; eauto with typeclass_instances. }
    forward_reason. clear H1.
    rewrite (ctx_subst_eta c) in *; simpl in *.
    generalize dependent (snd (fromExs c)).
    generalize dependent (fst (fromExs c)).
    intros. inv_all.
    split; auto.
    forward. inv_all. subst.
    assert (sem_preserves_if_ho
              (fun P : exprT (getUVars ctx ++ l) (getVars ctx) Prop =>
                 forall (us : hlist typD (getAmbientUVars ctx))
                        (vs : hlist typD (getAmbientVars ctx)),
                   e (fun us vs => forall z, P (hlist_app us z) vs) us vs) (fun u : uvar => subst_lookup u s)).
    { clear H7. red.
      intros.
      generalize H0.
      eapply pctxD_substD in H0; try eassumption.
      2: exact H2.
      destruct H0 as [ ? [ ? ? ] ].
      eapply substD_lookup
      with (SubstOk := @SubstOk_ctx_subst _ _ _ _ _ _ _) in H7;
        try eassumption.
      forward_reason.
      eapply nth_error_get_hlist_nth_weaken with (ls' := l) in H7.
      simpl in H7. rewrite H9 in H7.
      forward_reason. inv_all. subst.
      eapply exprD'_weakenU with (tus' := l) in H11; eauto.
      destruct H11 as [ ? [ ? ? ] ].
      eexists; split; eauto.
      intros. gather_facts. eapply Pure_pctxD; eauto.
      intros. rewrite <- H13; clear H13; eauto.
      rewrite <- H11; clear H11.
      eauto. }
    generalize (fun AC => @amap_instantiates_substD _ _ _ _ _ _ (getUVars ctx ++ l) (getVars ctx) _ AC (fun u : nat => ctx_lookup u s) _ _ _ _ H4 H8 H9).
    clear H9. destruct 1 as [ ? [ ? ? ] ].
    { clear - H0.
      revert H0. revert e; revert s; revert ctx; revert l.
      eapply ExprTApplicative_with_extra. }
    rewrite H9 in *.
    forward. inv_all; subst.
    forward_reason. inv_all; subst.
    split; eauto.
    intros. gather_facts.
    rewrite H0 in *. rewrite H9 in *.
    rewrite H12 in *. rewrite H7 in *.
    gather_facts.
    eapply subst_getInstantiation in H7;
      eauto using WellFormed_entry_WellFormed_pre_entry.
    destruct H7.
    eapply pctxD_SubstMorphism; eauto.
    gather_facts.
    eapply Pure_pctxD; eauto.
    clear - H7.
    intros. specialize (H7 us vs).
    eapply _exists_sem.
    exists (hlist_map
              (fun (t : typ) (x0 : exprT (getUVars ctx) (getVars ctx) (typD t)) =>
                 x0 us vs) x2).
    rewrite _forall_sem in H1.
    split.
    { eapply H. eapply H0. eapply H7. }
    { eapply H1. eapply H7. }
  Qed.

  Lemma rtac_spec_Exs_More
    : forall ctx (s : ctx_subst ctx) l a g c g',
      rtac_spec (remembers s l a) g (More_ c g') ->
      rtac_spec s (GExs l a g)
                (More_ (snd (fromExs c)) (GExs l (fst (fromExs c)) g')).
  Proof.
    unfold rtac_spec.
    Transparent remembers. unfold remembers. Opaque remembers.
    intros. inv_all.
    forward_reason.
    destruct H.
    { edestruct remembers_sound; eauto with typeclass_instances. }
    simpl in *.
    rewrite (ctx_subst_eta c) in *. simpl in *.
    generalize dependent (snd (fromExs c)).
    generalize dependent (fst (fromExs c)).
    clear c. intros; inv_all; subst.
    split; auto.
    forward_reason.
    split.
    { constructor; eauto using WellFormed_entry_WellFormed_pre_entry. }
    forward. inv_all. subst.
    assert (sem_preserves_if_ho
              (fun P : exprT (getUVars ctx ++ l) (getVars ctx) Prop =>
                 forall (us : hlist typD (getAmbientUVars ctx))
                        (vs : hlist typD (getAmbientVars ctx)),
                   e (fun us vs => forall z, P (hlist_app us z) vs) us vs) (fun u : uvar => subst_lookup u s)).
    { clear H7. red.
      intros.
      generalize H0.
      eapply pctxD_substD in H0; try eassumption.
      2: exact H1.
      destruct H0 as [ ? [ ? ? ] ].
      eapply substD_lookup
      with (SubstOk := @SubstOk_ctx_subst _ _ _ _ _ _ _) in H7;
        try eassumption.
      forward_reason.
      eapply nth_error_get_hlist_nth_weaken with (ls' := l) in H7.
      simpl in H7. rewrite H9 in H7.
      forward_reason. inv_all. subst.
      eapply exprD'_weakenU with (tus' := l) in H11; eauto.
      destruct H11 as [ ? [ ? ? ] ].
      eexists; split; eauto.
      intros. gather_facts. eapply Pure_pctxD; eauto.
      intros. rewrite <- H13; clear H13; eauto.
      rewrite <- H11; clear H11.
      eauto. }
    generalize (fun AC => @amap_instantiates_substD _ _ _ _ _ _ (getUVars ctx ++ l) (getVars ctx) _ AC (fun u : nat => ctx_lookup u s) _ _ _ _ H3 H8 H9).
    clear H9. destruct 1 as [ ? [ ? ? ] ].
    { clear - H0.
      revert H0. revert e; revert s; revert ctx; revert l.
      eapply ExprTApplicative_with_extra. }
    rewrite H9 in *.
    forward. inv_all; subst.
    forward_reason. inv_all; subst.
    split; eauto.
    intros. gather_facts.
    rewrite H0 in *. rewrite H9 in *.
    rewrite H13 in *. rewrite H7 in *.
    gather_facts.
    destruct H7.
    eapply pctxD_SubstMorphism; eauto.
    gather_facts.
    eapply Pure_pctxD; eauto.
    clear.
    intros.
    revert H2. eapply _exists_impl.
    rewrite _forall_sem in H1.
    intros. specialize (H x0).
    specialize (H0 x0).
    specialize (H1 x0).
    tauto.
  Qed.

End spec_lemmas.
