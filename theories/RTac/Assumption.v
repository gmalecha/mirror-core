Require Import ExtLib.Data.Sum.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.RTac.Core.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Subst_subst : Subst subst expr}.
  Context {SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst}.
  Context {SubstUpdate_subst : SubstUpdate subst expr}.
  Context {SubstUpdateOk_subst : @SubstUpdateOk _ _ _ _ Expr_expr Subst_subst _ _}.

  Section findHyp.
    Variable check : expr -> subst -> option subst.

    Fixpoint findHyp (ctx : Ctx typ expr) (s : subst) {struct ctx}
    : option subst :=
      match ctx with
        | CTop => None
        | CAll ctx' _ => findHyp ctx' s
        | CEx  ctx' _ => findHyp ctx' s
        | CHyp ctx' h => match check h s with
                           | None => findHyp ctx' s
                           | Some e => Some e
                         end
      end.
  End findHyp.

  Variable check : Ctx typ expr -> expr -> expr -> subst -> option subst.

  Definition ASSUMPTION : rtac typ expr subst :=
    fun ctx s gl =>
      match findHyp (check ctx gl) ctx s with
        | None => Fail
        | Some s' =>
          Solved s'
      end.
(*
  Definition exprD'_ctx (ctx : Ctx typ expr) (e : expr) (t : typ)
  : option (OpenT (getUVars ctx) (getVars ctx) (typD t)) :=
    exprD' (getUVars ctx) (getVars ctx) e t.
*)
  Hypothesis checkOk
  : forall ctx e1 e2 s s',
      check ctx e1 e2 s = Some s' ->
      WellFormed_subst s ->
      let (tus,tvs) := getEnvs ctx in
      WellFormed_subst s' /\
      forall v1 v2 sD,
        exprD' tus tvs e1 (@typ0 _ _ Prop _) = Some v1 ->
        exprD' tus tvs e1 (@typ0 _ _ Prop _) = Some v2 ->
        substD tus s = Some sD ->
        exists sD',
             substD tus s' = Some sD'
          /\ forall us vs,
               sD' us ->
               sD us /\
               v1 us vs = v2 us vs.

(*
  Lemma findHypOk
  : forall ctx tus tvs g s s',
      findHyp (check ctx (** TODO: This isn't right **) g) ctx s = Some s' ->
      WellFormed_subst s ->
      WellFormed_subst s' /\
      let tus' := tus ++ getUVars ctx nil in
      let tvs' := tvs ++ getVars ctx nil in
      match propD  tus' tvs' g
          , substD tus' tvs' s
          , substD tus' tvs' s'
      with
        | Some gD , Some sD , Some sD' =>
          ctxD' ctx (fun (us : hlist _ (rev tus')) (vs : hlist _ (rev tvs')) =>
                       let us := hlist_unrev us in
                       let vs := hlist_unrev vs in
                       sD' us vs ->
                       sD us vs /\ gD us vs)
        | None , _ , _
        | _ , None , _ => True
        | Some _ , Some _ , None => False
      end.
  Proof.
    induction ctx; simpl; intros; try congruence.
    { specialize (IHctx tus (tvs ++ t :: nil) _ _ _ H H0).
      forward_reason; split; eauto.
      forward.
      subst.
      eapply substD_weakenV with (tvs' := t :: nil) in H4.
      eapply exprD'_typ0_weakenV with (tvs' := t :: nil) in H3.
      forward_reason.
      rewrite H4 in H2.
      change_rewrite H3 in H2.
      forwardy.
      rewrite 
 }
    { specialize (IHctx (tus ++ t :: nil) tvs _ _ _ H H0).
      forward_reason; split; eauto.
      forward.
      subst. eapply H4. }
    { consider (check ctx g e s); intros.
      { clear IHctx. inv_all; subst.
        eapply checkOk in H; clear checkOk; eauto.
        forward_reason; split; eauto.
        forward.
        destruct o0; inv_all; subst.
        { admit. }
        { 


  Theorem ASSUMPTION_sound : rtac_sound nil nil ASSUMPTION.
  Proof.
    unfold ASSUMPTION, rtac_sound.
    intros. subst.
    consider (findHyp s ctx g); auto.
    intros.
*)
End parameterized.
