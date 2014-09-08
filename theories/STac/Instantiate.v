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
Require Import MirrorCore.Lemma.
Require Import MirrorCore.LemmaApply.
Require Import MirrorCore.InstantiateI.
Require Import MirrorCore.STac.Core.
Require Import MirrorCore.STac.Continuation.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.
  Variable RType_typ : RType typ.
  Variable Typ0_Prop : Typ0 _ Prop.
  Let tyProp : typ := @typ0 _ _ _ _.

  Variable vars_to_uvars : nat -> nat -> expr -> expr.
  Variable exprUnify : tenv typ -> tenv typ -> nat -> expr -> expr -> typ -> subst -> option subst.
  Variable instantiate : (nat -> option expr) -> nat -> expr -> expr.

  Section instantiate.
    Variable Subst_subst : Subst subst expr.
    Variable SU : SubstUpdate subst expr.

    (** Think of this like:
     **   apply lem ; cont
     ** i.e. first apply the lemma and then require that all side-conditions
     ** except the last are solved by the prover [tac], currently with
     ** empty facts.
     **)
    Definition INSTANTIATE
    : stac typ expr subst :=
      fun tus tvs sub hs e =>
        let inst := instantiate (fun u => lookup u sub) 0 in
        More tus tvs sub (List.map inst hs) (inst e).
  End instantiate.

  Variable Expr_expr : Expr RType_typ expr.
  Variable ExprOk_expr : ExprOk Expr_expr.
  Variable Subst_subst : Subst subst expr.
  Variable SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst.

  Hypothesis exprD'_instantiate : exprD'_instantiate _ _ instantiate.

  Theorem INSTANTIATE_sound
  : stac_sound (INSTANTIATE _).
  Proof.
    intros. red; simpl.
    intuition.
    forward.
    unfold stateD in *.
    Require Import MirrorCore.Util.Forwardy.
    forwardy.
    inv_all; subst.
    admit. 
  Qed.

End parameterized.