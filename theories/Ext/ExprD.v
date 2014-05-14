Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Ext.ExprCore.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.ExprT.
Require Import MirrorCore.Ext.ExprDFacts.
Require MirrorCore.Ext.ExprD3.

Set Implicit Arguments.
Set Strict Implicit.

Module EXPR_DENOTE := Build_ExprDenote ExprD3.EXPR_DENOTE_core.

Include EXPR_DENOTE.

Existing Instance Expr_expr.

Theorem ExprOk_expr ts func (RSym_func : RSym (typD ts) func)
: @ExprOk _ _ _ (@Expr_expr ts func RSym_func).
Proof.
  constructor.
  { eapply EXPR_DENOTE.exprD'_weaken. }
Qed.

Create HintDb exprD_rw discriminated.

Hint Rewrite exprD_Var exprD_App exprD_UVar exprD_Sym : exprD_rw.
Hint Rewrite exprD'_Abs exprD'_Var exprD'_App exprD'_UVar exprD'_Sym : exprD_rw.
Hint Rewrite typ_cast_typ_refl typ_cast_typ_neq using congruence : exprD_rw.
