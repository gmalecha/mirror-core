Require Import MirrorCore.ExprI.
Require Import MirrorCore.Ext.ExprCore.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.ExprT.
Require Import MirrorCore.Ext.ExprD3.

Set Implicit Arguments.
Set Strict Implicit.

Include EXPR_DENOTE.

Instance Expr_expr ts (fs : functions ts) : Expr (typD ts) expr :=
{ exprD := exprD fs
; Safe_expr := WellTyped_expr (typeof_funcs fs)
; acc := expr_acc
; wf_acc := wf_expr_acc
}.

Create HintDb exprD_rw discriminated.

Hint Rewrite exprD_Var exprD_App exprD_UVar exprD_Equal exprD_Not exprD_Func : exprD_rw.
Hint Rewrite exprD'_Abs exprD'_Var exprD'_App exprD'_UVar exprD'_Equal exprD'_Not exprD'_Func : exprD_rw.
