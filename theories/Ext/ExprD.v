Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Ext.ExprCore.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.ExprT.
Require Import MirrorCore.Ext.ExprDFacts.
Require Import MirrorCore.Ext.ExprD3.

Set Implicit Arguments.
Set Strict Implicit.

Module EXPR_DENOTE := Build_ExprDenote EXPR_DENOTE_core.

Include EXPR_DENOTE.

Instance Expr_expr ts func (RSym_func : RSym (typD ts) func) : Expr (typD ts) (expr func) :=
{ exprD := exprD
; Safe_expr := @WellTyped_expr _ _ RSym_func
; acc := @expr_acc _
; wf_acc := @wf_expr_acc _
}.

Theorem ExprOk_expr ts func (RSym_func : RSym (typD ts) func)
: @ExprOk _ _ _ (@Expr_expr ts func RSym_func).
Proof.
  constructor.
  { eapply EXPR_DENOTE.typeof_expr_exprD. }
  { admit. } (** TODO: this is weakening... *)
Qed.

Create HintDb exprD_rw discriminated.

Hint Rewrite exprD_Var exprD_App exprD_UVar exprD_Sym : exprD_rw.
Hint Rewrite exprD'_Abs exprD'_Var exprD'_App exprD'_UVar exprD'_Sym : exprD_rw.
Hint Rewrite typ_cast_typ_refl typ_cast_typ_neq using congruence : exprD_rw.
