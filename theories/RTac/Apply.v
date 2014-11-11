Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.LemmaApply.
Require Import MirrorCore.InstantiateI.
Require Import MirrorCore.VariablesI.
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
  Context {Expr_expr : Expr RType_typ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {ExprUVar_expr : ExprUVar expr}.

  Variable vars_to_uvars : nat -> nat -> expr -> expr.
  Variable exprUnify : forall subst, Subst subst expr -> SubstUpdate subst expr ->
    tenv typ -> tenv typ -> nat -> expr -> expr -> typ -> subst -> option subst.
  Variable instantiate : (nat -> option expr) -> nat -> expr -> expr.

  Variable vars_to_uvars_sound : vars_to_uvars_spec vars_to_uvars.
  Variable exprUnify_sound
  : forall subst S (SO : SubstOk S) SU (SUO : SubstUpdateOk _ SO),
      unify_sound (@exprUnify subst S SU).


  Variable lem : Lemma.lemma typ expr expr.

  Definition APPLY : rtac typ expr :=
    @EAPPLY typ expr _ _ _ vars_to_uvars exprUnify instantiate lem.

  Hypothesis lemD :
    @Lemma.lemmaD typ expr _ _ expr (@exprD'_typ0 _ _ _ _ Prop _)
                  _ nil nil lem.

  Theorem APPLY_sound : rtac_sound APPLY.
  Proof.
    eapply EAPPLY_sound; eauto.
  Qed.

End parameterized.
