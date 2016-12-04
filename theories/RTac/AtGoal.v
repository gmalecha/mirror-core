Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.RTac.Core.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Set.
  Variable expr : Set.

  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {ExprUVar_expr : ExprUVar expr}.

  Variable tac
  : forall ctx : Ctx typ expr, ctx_subst ctx -> expr
                               -> rtac typ expr.

  Definition AT_GOAL
  : rtac typ expr :=
    fun ctx s e => (@tac ctx s e) ctx s e.

  Hypothesis tac_sound : forall c s e, rtac_sound (@tac c s e).

  Theorem AT_GOAL_sound : rtac_sound AT_GOAL.
  Proof.
    unfold AT_GOAL; simpl.
    red. intros; subst.
    eapply tac_sound. reflexivity.
  Qed.

End parameterized.

Typeclasses Opaque AT_GOAL.
Hint Opaque AT_GOAL : typeclass_instances.

Arguments AT_GOAL {typ expr} _%rtac _ _ _.
