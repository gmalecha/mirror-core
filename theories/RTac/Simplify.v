Require Import ExtLib.Data.Sum.
Require Import ExtLib.Tactics.
Require Import MirrorCore.RTac.Core.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Context {typ : Type}.
  Context {expr : Type}.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Expr_expr : Expr typ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.
  Context {ExprVar_expr : ExprVar expr}.
  Context {ExprVarOk_expr : ExprVarOk _}.
  Context {ExprUVar_expr : ExprUVar expr}.

  Definition reducer : Type :=
    forall subst : Type,
      Subst subst expr ->
      Ctx typ expr -> subst -> expr -> expr.
  Definition reducer_sound (r : reducer) : Prop :=
    forall (ctx : Ctx typ expr) (s : ctx_subst ctx) e e' cD sD eD,
      r (ctx_subst ctx) _ ctx s e = e' ->
      WellFormed_subst s ->
      @pctxD typ expr RType_typ _ Expr_expr ctx s = Some cD ->
      ctx_substD (getUVars ctx) (getVars ctx) s = Some sD ->
      propD (getUVars ctx) (getVars ctx) e = Some eD ->
      exists eD',
        propD (getUVars ctx) (getVars ctx) e' = Some eD' /\
        forall us vs,
          cD (fun us vs => sD us vs -> (eD' us vs -> eD us vs)) us vs.

  Variable simplify : reducer.

  Definition SIMPLIFY : rtac typ expr :=
    fun ctx sub gl =>
      More_ sub (GGoal (@simplify (ctx_subst ctx) _ ctx sub gl)).

  Hypothesis simplify_sound' : reducer_sound simplify.

  Lemma simplify_sound
  : forall (ctx : Ctx typ expr) (s : ctx_subst ctx) e e',
      @simplify (ctx_subst ctx) _ ctx s e = e' ->
      WellFormed_subst s ->
      match @pctxD typ expr RType_typ _ Expr_expr ctx s
          , ctx_substD (getUVars ctx) (getVars ctx) s (* necessary? *)
          , propD (getUVars ctx) (getVars ctx) e
          , propD (getUVars ctx) (getVars ctx) e'
      with
        | None , _ , _ , _ => True
        | _ , None , _ , _ => True
        | _ , _ , None , _ => True
        | _ , _ , _ , None => False
        | Some cD , Some sD , Some eD , Some eD' =>
          forall us vs,
            cD (fun us vs => sD us vs -> (eD' us vs -> eD us vs)) us vs
      end.
  Proof.
    intros. forward.
    eapply simplify_sound' in H; eauto.
    forward_reason.
    rewrite H. eauto.
  Qed.

  Theorem SIMPLIFY_sound : rtac_sound SIMPLIFY.
  Proof.
    generalize simplify_sound. clear simplify_sound'.
    intro simplify_sound.
    red; intros; subst.
    simpl. intros; split; eauto.
    remember (simplify (Subst_ctx_subst ctx) ctx s g).
    symmetry in Heqe.
    specialize (@simplify_sound _ _ _ _ Heqe).
    forward.
    specialize (@simplify_sound H0).
    split; try constructor.
    forward.
    destruct (pctxD_substD H0 H1) as [ ? [ ? ? ] ].
    revert simplify_sound0.
    change_rewrite H3.
    intros; forward.
    split.
    { reflexivity. }
    { intros. specialize (@simplify_sound0 us vs); revert simplify_sound0.
      eapply Ap_pctxD; eauto.
      specialize (H4 us vs); revert H4.
      eapply Ap_pctxD; eauto.
      eapply Pure_pctxD; eauto. }
  Qed.

End parameterized.

Typeclasses Opaque SIMPLIFY.
Hint Opaque SIMPLIFY.

Arguments reducer _ _ : clear implicits.
Arguments reducer_sound {_ _ _ _ _ _ _} _ : clear implicits.