Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.LemmaApply.
Require Import MirrorCore.UnifyI.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.Reduce.
Require Import MirrorCore.RTac.EApply.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.

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
  : forall subst (S : Subst subst expr) (SO : SubstOk subst typ expr) SU (SUO : SubstUpdateOk subst typ expr),
      unify_sound (@exprUnify subst S SU).

  Variable lem : Lemma.lemma typ expr expr.

  Definition APPLY : rtac typ expr :=
    (** TODO(gmalecha): This can be more efficient because APPLY is not supposed
     ** to introduce new unification variables
     **)
    @EAPPLY typ expr _ _ _ _ exprUnify lem.

  Hypothesis lemD : ReifiedLemma lem.

  Theorem APPLY_sound : rtac_sound APPLY.
  Proof.
    eapply EAPPLY_sound; eauto.
  Qed.

End parameterized.

Hint Opaque APPLY : typeclass_instances.

Arguments APPLY {typ expr _ _ _ _} unify lem _ _ _ : rename.