Require Import ExtLib.Data.Sum.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.RTac.Core.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.

  Section findHyp.
    Variable T : Type.
    Variable check : expr -> option T.

    Fixpoint findHyp (ctx : Ctx typ expr) {struct ctx}
    : option T :=
      match ctx with
        | CTop _ _ => None
        | CAll ctx' _ => @findHyp ctx'
        | CExs ctx' _ => @findHyp ctx'
        | CHyp ctx' h' =>
          match check h' with
            | None => @findHyp ctx'
            | Some s'' => Some s''
          end
      end.
  End findHyp.

  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Expr_expr : Expr typ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.

  Variable check : forall {subst : Type} {S : Subst subst expr} {SU : SubstUpdate subst expr},
                     Ctx typ expr -> expr -> expr -> subst -> option subst.

  Let SubstUpdate_ctx_subst ctx :=
    @SubstUpdate_ctx_subst typ _ _ _ ctx.
  Local Existing Instance SubstUpdate_ctx_subst.

  Definition EASSUMPTION : rtac typ expr :=
    fun _ _ _ _ ctx s gl =>
      match @findHyp (ctx_subst ctx)
                     (fun e => @check _ _ _ ctx gl e s) ctx with
        | None => Fail
        | Some s' => Solved s'
      end.

  Hypothesis checkOk
  : forall ctx e1 e2 s s',
      @check (ctx_subst ctx) _ _ ctx e1 e2 s = Some s' ->
      WellFormed_subst s ->
      let tus := getUVars ctx in
      let tvs := getVars ctx in
      WellFormed_subst s' /\
      forall v1 v2 sD,
        propD tus tvs e1 = Some v1 ->
        propD tus tvs e2 = Some v2 ->
        substD tus tvs s = Some sD ->
        substR tus tvs s s' /\
        exists sD',
             substD tus tvs s' = Some sD'
          /\ forall us vs,
               sD' us vs ->
               sD us vs /\
               v1 us vs = v2 us vs.

  Lemma findHypOk
  : forall g (ctx ctx' : Ctx typ expr)
           (s s' : ctx_subst (Ctx_append ctx ctx')),
      findHyp (T:=ctx_subst (Ctx_append ctx ctx'))
              (fun g' => @check _ _ _ (Ctx_append ctx ctx') g g' s)
              ctx = Some s' ->
      getAmbient ctx' = getEnvs ctx ->
      WellFormed_subst s ->
      WellFormed_subst s' /\
      match propD  _ _ g
          , pctxD s
          , pctxD s'
      with
        | Some gD , Some sD , Some sD' =>
          SubstMorphism s s' /\
          forall us vs, sD' gD us vs
        | None , _ , _
        | _ , None , _ => True
        | Some _ , Some _ , None => False
      end.
  Proof.
    induction ctx; simpl; intros; try congruence.
    { specialize (@IHctx (Ctx_append (CAll (CTop (getUVars ctx) (getVars ctx)) t) ctx')).
      rewrite Ctx_append_assoc in IHctx. simpl in IHctx.
      destruct (IHctx s s' H); eauto.
      simpl in *.
      rewrite getAmbient_Ctx_append. simpl.
      symmetry. apply getEnvs_getUVars_getVars. }
    { specialize (@IHctx (Ctx_append (CExs (CTop (getUVars ctx) (getVars ctx)) t) ctx')).
      rewrite Ctx_append_assoc in IHctx. simpl in IHctx.
      destruct (IHctx s s' H); eauto.
      simpl in *.
      rewrite getAmbient_Ctx_append. simpl.
      symmetry. apply getEnvs_getUVars_getVars. }
    { consider (check (Subst_ctx_subst (Ctx_append (CHyp ctx e) ctx'))
          (SubstUpdate_ctx_subst (Ctx_append (CHyp ctx e) ctx'))
          (Ctx_append (CHyp ctx e) ctx') g e s); intros.
      { inv_all; subst.
        clear IHctx.
        eapply checkOk in H; clear checkOk; eauto.
        forward_reason; split; auto.
        forward.
        destruct (pctxD_substD H1 H4) as [ ? [ ? ? ] ].
        specialize (fun v2 H => @H3 _ v2 _ eq_refl H H5).
        destruct (pctxD_get_hyp _ _ _ H1 H4) as [ ? [ ? ? ] ].
        change (getUVars ctx) with (getUVars (CHyp ctx e)) in H7.
        change (getVars ctx) with (getVars (CHyp ctx e)) in H7.
        eapply propD_weaken_by_Ctx_append in H7; eauto.
        forward_reason.
        eapply H3 in H7.
        forward_reason.
        destruct (substD_pctxD _ H H4 H10) as [ ? [ ? ? ] ].
        rewrite H12. split; try eassumption.
        intros. gather_facts.
        eapply pctxD_SubstMorphism; [ eapply H7 | |  | ]; eauto.
        gather_facts.
        eapply Pure_pctxD; eauto.
        clear - H11 H9.
        intros; eauto.
        eapply H11 in H1.
        destruct H1. rewrite H2; clear H2.
        eapply H9. eauto. }
      { specialize (@IHctx (Ctx_append (CHyp (CTop (getUVars ctx) (getVars ctx)) e) ctx')).
        rewrite Ctx_append_assoc in IHctx. simpl in *.
        eapply IHctx; eauto.
        rewrite getAmbient_Ctx_append. simpl.
        symmetry. eapply getEnvs_getUVars_getVars. } }
  Qed.

  Theorem ASSUMPTION_sound : rtac_sound EASSUMPTION.
  Proof.
    unfold EASSUMPTION, rtac_sound.
    intros. subst.
    red. simpl.
    forward.
    eapply findHypOk with (ctx' := CTop (getUVars ctx) (getVars ctx)) in H; eauto.
    { forward_reason; split; auto.
      forward. clear - H2 H3. exfalso.
      change_rewrite H2 in H3. congruence. }
    { simpl. symmetry.
      eapply getEnvs_getUVars_getVars. }
  Qed.

End parameterized.
