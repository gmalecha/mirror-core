Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.LemmaApply.
Require Import MirrorCore.InstantiateI.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.Reduce.
Require Import MirrorCore.RTac.EApply.

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
  Context {SU : SubstUpdate subst expr}.
  Context {SubstUpdateOk_subst : @SubstUpdateOk _ _ _ _ Expr_expr Subst_subst _ _}.

  Variable UVar : nat -> expr.
  Variable vars_to_uvars : nat -> nat -> expr -> expr.
  Variable exprUnify : forall subst, Subst subst expr -> SubstUpdate subst expr ->
    tenv typ -> tenv typ -> nat -> expr -> expr -> typ -> subst -> option subst.
  Variable instantiate : (nat -> option expr) -> nat -> expr -> expr.

  Variable lem : Lemma.lemma typ expr expr.

  Definition APPLY : rtac typ expr subst :=
    @EAPPLY typ expr subst _ _ _ _ UVar vars_to_uvars exprUnify instantiate lem.

  Hypothesis lemD :
    @Lemma.lemmaD typ expr _ _ expr (@exprD'_typ0 _ _ _ _ Prop _)
                  _ nil nil lem.

  Theorem APPLY_sound : rtac_sound nil nil APPLY.
  Proof.
    eapply EAPPLY_sound.
  Qed.

End parameterized.
