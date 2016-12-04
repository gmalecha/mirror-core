Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.VariablesI.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.LemmaApply.
Require Import MirrorCore.Instantiate.
Require Import MirrorCore.VarsToUVars.
Require Import MirrorCore.UnifyI.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.Reduce.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Set.
  Variable expr : Set.

  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Expr_expr : Expr typ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.
  Context {ExprUVar_expr : ExprUVar expr}.
  Context {ExprUVarOk_expr : ExprUVarOk _}.

  Variable exprUnify : forall subst, Subst subst expr -> SubstUpdate subst expr ->
    unifier typ expr subst.

  Variable exprUnify_sound
  : forall subst (S : Subst subst expr) (SO : SubstOk subst typ expr) SU
           (SUO : SubstUpdateOk subst typ expr),
      unify_sound (@exprUnify subst S SU).

  Variable lem : Lemma.lemma typ expr expr.

  Definition freshUVars (ts : list typ) (c : Ctx typ expr) (s : ctx_subst c)
  : ctx_subst (CExs c ts) :=
    ExsSubst s (amap_empty _).

  Definition EAPPLY : rtac typ expr :=
    let len_vars := length lem.(vars) in
    fun ctx sub goal =>
      let (tus,tvs) := getEnvs ctx in
      let nus := length tus in
      match @eapplicable typ expr _ _
                         _ _ _
                         (@exprUnify _ _ (SubstUpdate_ctx_subst _))
                         (freshUVars lem.(vars) sub)
                         tus tvs lem goal
      with
      | None => Fail
      | Some sub' =>
        let premises :=
            map (fun e => GGoal (vars_to_uvars 0 nus e)) lem.(premises)
        in
        reduceResult (* instantiate UVar *)
          ctx (CExs (CTop tus tvs) lem.(vars))
          (GConj_list premises) sub'
      end.

  Class ReifiedLemma (L : lemma typ expr expr) : Prop := mkRL
  { ReifiedLemma_proof : lemmaD (@exprD_typ0 _ _ _ _ Prop _) nil nil L }.

  Hypothesis lemD : ReifiedLemma lem.

  Lemma goalD_GConj_list tus tvs C (ExprTApp : CtxLogic.ExprTApplicative C)
  : forall ls gsD,
      List.mapT_list (F:=option) (goalD tus tvs) ls = Some gsD ->
      exists gsD',
        goalD tus tvs (GConj_list (expr:=expr) ls) = Some gsD' /\
        C (fun us vs =>
             gsD' us vs <-> Forall (fun x => x us vs) gsD).
  Proof.
    induction ls; simpl; intros.
    - inv_all; subst.
      eexists; split; eauto.
      eapply CtxLogic.exprTPure. intros.
      clear. intuition.
    - forward; inv_all; subst.
      specialize (IHls _ eq_refl).
      forward_reason. destruct ls.
      + rewrite H. eexists; split; eauto.
        eapply CtxLogic.exprTPure.
        simpl in H1. inv_all; subst.
        intros. intuition. inversion H0; subst; auto.
      + simpl in *. rewrite H.
        rewrite H1. eexists; split; eauto.
        revert H2.
        eapply CtxLogic.exprTAp.
        forward; inv_all; subst.
        eapply CtxLogic.exprTPure.
        clear. intros. rewrite H.
        clear. split.
        { constructor; tauto. }
        { inversion 1; tauto. }
  Qed.

  Lemma WellFormed_Goal_GConj_list tus tvs l :
    Forall (WellFormed_Goal (typ:=typ) tus tvs) l ->
    WellFormed_Goal tus tvs (GConj_list l).
  Proof using.
    induction 1; simpl.
    - constructor.
    - destruct l; auto.
      constructor; auto.
  Qed.

  Lemma mapT_list_map
  : forall {T U V} (g : T -> U) (f : U -> option V) ls,
      List.mapT_list (fun x => f (g x)) ls =
      List.mapT_list f (map g ls).
  Proof using.
    induction ls; simpl; intros; auto.
    destruct (f (g a)); auto.
    rewrite IHls. reflexivity.
  Qed.

  Theorem EAPPLY_sound : rtac_sound EAPPLY.
  Proof.
    red. unfold EAPPLY. intros.
    subst. unfold rtac_spec. forward.
    unfold reduceGoal.
    rewrite (ctx_subst_eta c). simpl.
    intros.
    eapply Proper_rtac_spec.
    { reflexivity. }
    { eapply More_More_. reflexivity. }
    eapply rtac_spec_rtac_spec_modular; eauto.
    unfold rtac_spec_modular.
    Opaque GoalImplies. simpl.
    eapply Transitive_GoalImplies;
    [ eauto | eapply GoalImplies_GExs_do_solved ]; eauto.
    Transparent GoalImplies. simpl.
    intros.
    eapply eapplicable_sound'
      with (Expr_expr:=Expr_expr)
           (Subst_subst:=Subst_ctx_subst _)
           (SubstOk_subst:=SubstOk_ctx_subst _)
           (unify:=@exprUnify _ _ (SubstUpdate_ctx_subst _)) in H0;
      eauto.
    { rewrite (ctx_subst_eta c) in H0; simpl in *.
      forward_reason; inv_all; subst.
      split; auto.
      split.
      { constructor; auto.
        rewrite <- countUVars_getUVars.
        rewrite countUVars_getUVars.
        eapply WellFormed_entry_WellFormed_pre_entry; eauto.
        eapply WellFormed_Goal_GConj_list. clear.
        induction (premises lem); simpl; constructor.
        - constructor.
        - auto. }
      simpl in *. forward.
      destruct (drop_exact_append_exact (vars lem) t) as [ ? [ ? ? ] ].
      destruct (pctxD_substD H2 H0) as [ ? [ ? ? ] ].
      eapply exprD_typ0_weakenU with (tus' := lem.(vars)) in H6.
      destruct H6 as [ ? [ ? ? ] ].
      rewrite getEnvs_getUVars_getVars in H. inversion H. subst.
      forward_reason.
      repeat match goal with
               | H : _ = _ , H' : _ |- _ =>
                 rewrite H in H'
             end.
      destruct lemD as [ lemD' ]; clear lemD; rename lemD' into lemD.
      specialize (H3 _ _ lemD eq_refl eq_refl).
      forward_reason. forwardy. inv_all; subst.
      destruct (substD_pctxD _ H4 H0 H15) as [ ? [ ? ? ] ].
      rewrite H. inv_all; subst.
      change_rewrite H12.
      rewrite H0 in *. rewrite H12 in *. simpl in H3.
      rewrite H in H3.
      assert (GOALSD : List.mapT_list (goalD (getUVars ctx ++ vars lem) (getVars ctx))
                                      (map
                                         (fun e3 : expr => GGoal (vars_to_uvars 0 (length (getUVars ctx)) e3))
                                         (premises lem)) = Some x3).
      { rewrite <- mapT_list_map. simpl. assumption. }
      destruct (fun Z => @goalD_GConj_list
                           (getUVars ctx ++ vars lem) (getVars ctx)
                           (fun P => forall us vs, x2 (fun us vs => forall us', P (HList.hlist_app us us') vs) us vs) Z
                           _ _ GOALSD) as [ ? [ ? ? ] ]; clear GOALSD.
      { constructor; intros.
        eapply Pure_pctxD; eauto.
        gather_facts.
        eapply Pure_pctxD; eauto. }
      change_rewrite H18.
      split.
      { simpl. assumption. }
        intros. gather_facts.
        eapply Pure_pctxD; eauto.
        intros.
        eapply Quant._exists_sem in H22. destruct H22.
        repeat match goal with
                 | H : forall x, _ , H' : _ |- _ =>
                   specialize (H H')
               end.
        rewrite H11; clear H11.
        rewrite H8 in *; clear H8.
        destruct H14. tauto. tauto. }
    { unfold freshUVars. constructor; eauto.
      eapply WellFormed_entry_amap_empty; eauto. }
  Qed.

End parameterized.

Typeclasses Opaque EAPPLY.
Hint Opaque EAPPLY : typeclass_instances.

Arguments EAPPLY {typ expr _ _ _ _} unify lem _ _ _ : rename.
