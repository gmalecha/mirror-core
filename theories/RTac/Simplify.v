Require Import ExtLib.Data.Sum.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SubstI.
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

  Hypothesis simplify_sound : False.

  Theorem SIMPLIFY_sound
  : forall tus tvs, rtac_sound tus tvs SIMPLIFY.
  Proof.
  Admitted.

End parameterized.
