Require Import ExtLib.Data.Sum.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.UnifyI.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.RTac.Core.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Set.
  Variable expr : Set.

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

  Variable exprUnify : forall subst, Subst subst expr -> SubstUpdate subst expr ->
    unifier typ expr subst.

  Let SubstUpdate_ctx_subst ctx :=
    @SubstUpdate_ctx_subst typ _ _ _ ctx.
  Local Existing Instance SubstUpdate_ctx_subst.

  Definition EASSUMPTION : rtac typ expr :=
    fun ctx s gl =>
      match findHyp
              (fun e => @exprUnify _ _ _ (getUVars ctx) (getVars ctx) 0 gl e (typ0 (F:=Prop)) s) ctx
      with
        | None => Fail
        | Some s' => Solved s'
      end.

  Variable exprUnify_sound
  : forall subst (S : Subst subst expr) (SO : SubstOk subst typ expr) SU
           (SUO : SubstUpdateOk subst typ expr),
      unify_sound (@exprUnify subst S SU).

  Lemma findHypOk
  : forall g (ctx ctx' : Ctx typ expr)
           (s s' : ctx_subst (Ctx_append ctx ctx')),
      findHyp (T:=ctx_subst (Ctx_append ctx ctx'))
              (fun e => @exprUnify _ _ _ (getUVars (Ctx_append ctx ctx'))
                                   (getVars (Ctx_append ctx ctx')) 0 g e (typ0 (F:=Prop)) s)
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
    { match goal with
      | [ H: match ?X with _ => _ end = _ |- _ ] => destruct X eqn:?
      end.
      { inv_all; subst.
        clear IHctx.
        specialize (@exprUnify_sound _ _ _ _ _ _ _ _ _ _ _ _ nil Heqo).
        destruct (@exprUnify_sound H1); clear exprUnify_sound.
        split; auto.
        forward.
        destruct (pctxD_substD H1 H4) as [ ? [ ? ? ] ].
        destruct (@pctxD_get_hyp _ _ _ _ _ _ _ _ _ _ _ _ H1 H4); eauto.
        forward_reason.
        eapply propD_weaken_by_Ctx_append with (ctx := CHyp ctx e) in H7; eauto.
        forward_reason.
        simpl in *.
        unfold propD, exprD_typ0 in *.
        forward; inv_all. subst.
        specialize (@H11 _ _ _ eq_refl eq_refl H5).
        forward_reason.
        destruct (substD_pctxD _ H H4 H10) as [ ? [ ? ? ] ].
        rewrite H12.
        split; [ assumption | ].
        intros.
        gather_facts.
        eapply pctxD_SubstMorphism; [ eassumption | | | ]; eauto.
        gather_facts.
        eapply Pure_pctxD; eauto.
        intros.
        destruct (H11 _ _ H13); clear H11.
        specialize (H15 Hnil); simpl in H15.
        eapply H9 in H8.
        revert H8. revert H15.
        clear.
        do 2 rewrite eq_exprT_eq.
        intro. rewrite H15. clear. tauto. }
      { specialize
          (@IHctx (Ctx_append (CHyp (CTop (getUVars ctx) (getVars ctx)) e) ctx')).
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

Typeclasses Opaque EASSUMPTION.
Hint Opaque EASSUMPTION : typeclass_instances.
