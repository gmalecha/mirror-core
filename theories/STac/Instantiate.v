Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.ListMapT.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.InstantiateI.
Require Import MirrorCore.STac.Core.
Require Import MirrorCore.STac.Simplify.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.
  Variable RType_typ : RType typ.
  Variable Typ0_Prop : Typ0 _ Prop.
  Let tyProp : typ := @typ0 _ _ _ _.

  Variable instantiate : (nat -> option expr) -> nat -> expr -> expr.

  Section instantiate.
    Variable Subst_subst : Subst subst expr.
    Variable SU : SubstUpdate subst expr.

    Definition INSTANTIATE
    : stac typ expr subst :=
      @SIMPLIFY typ expr subst
                (fun tus tvs sub => instantiate (fun u => lookup u sub) 0).
  End instantiate.

  Variable Expr_expr : Expr RType_typ expr.
  Variable ExprOk_expr : ExprOk Expr_expr.
  Variable Subst_subst : Subst subst expr.
  Variable SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst.

  Hypothesis exprD'_instantiate : exprD'_instantiate _ _ instantiate.

  Theorem INSTANTIATE_sound
  : stac_sound (INSTANTIATE _).
  Proof.
    eapply SIMPLIFY_sound.
    intros. unfold propD.
    forward.
    eapply sem_preserves_if_substD in H2; eauto.
    red in exprD'_instantiate.
    unfold ExprDAs.exprD'_typ0 in *.
    forward.
    eapply exprD'_instantiate with (tvs' := nil) in H1; eauto.
    simpl in H1.
    forward_reason.
    subst. rewrite H1.
    intros.
    inv_all; subst.
    autorewrite with eq_rw.
    specialize (H4 us vs Hnil).
    simpl in *.
    rewrite H4; auto. reflexivity.
  Qed.

End parameterized.