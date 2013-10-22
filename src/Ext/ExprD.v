Require Import MirrorCore.ExprI.
Require Import MirrorCore.Ext.ExprCore.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.ExprT.
Require Import MirrorCore.Ext.ExprD3.

Set Implicit Arguments.
Set Strict Implicit.

Include EXPR_DENOTE.

Instance Expr_expr ts func (RFunc_func : RFunc (typD ts) func) : Expr (typD ts) (expr func) :=
{ exprD := exprD
; Safe_expr := @WellTyped_expr _ _ RFunc_func
; acc := @expr_acc _
; wf_acc := @wf_expr_acc _
}.

Create HintDb exprD_rw discriminated.

Hint Rewrite exprD_Var exprD_App exprD_UVar exprD_Func : exprD_rw.
Hint Rewrite exprD'_Abs exprD'_Var exprD'_App exprD'_UVar exprD'_Func : exprD_rw.
