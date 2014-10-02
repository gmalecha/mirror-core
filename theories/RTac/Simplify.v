Require Import ExtLib.Data.Sum.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.RTac.Core.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Context {typ : Type}.
  Context {expr : Type}.
  Context {subst : Type}.
  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Subst_subst : Subst subst expr}.
  Context {SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst}.

  Variable simplify : Ctx typ expr -> subst -> expr -> expr.

  Definition SIMPLIFY : rtac typ expr subst :=
    fun ctx sub gl => More sub (GGoal (simplify ctx sub gl)).

  Variable tus : tenv (ctyp typ).
  Variable tvs : tenv typ.

  Hypothesis simplify_sound
  : forall ctx sub e,
      let '(tus',tvs') := getEnvs ctx in
      forall eD sD,
      exprD'_typ0 Prop (tus ++ tus') (tvs ++ tvs') e = Some eD ->
      substD (tus ++ tus') sub = Some sD ->
      exists eD',
        exprD'_typ0 Prop (tus ++ tus') (tvs ++ tvs') (simplify ctx sub e) = Some eD' /\
        forall us vs,
          sD us ->
          eD us vs = eD' us vs.

  Theorem SIMPLIFY_sound
  : rtac_sound tus tvs SIMPLIFY.
  Proof.
    unfold rtac_sound, SIMPLIFY.
    intros; subst.
    split; eauto.
    specialize (simplify_sound ctx s g).
    destruct (getEnvs ctx).
    forward.
    eapply simplify_sound in H0; eauto.
    forward_reason.
    change_rewrite H0.
    eapply ctxD'_no_hyps. intuition.
    rewrite H2; eauto.
  Qed.

End parameterized.
