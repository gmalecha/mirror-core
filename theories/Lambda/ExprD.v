Require Import MirrorCore.ExprI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Lambda.TypesI2.
Require Import MirrorCore.Lambda.ExprCore.
Require MirrorCore.Lambda.ExprDsimul.

Set Implicit Arguments.
Set Strict Implicit.

(** Here I need my instance **)
Export ExprDsimul.ExprDenote.

Section Expr.
  Context {typ : Type}
          {typD : list Type -> typ -> Type}
          {func : Type}.
  Context {RT : RType typD}
          {T2 : Typ2 typD PreFun.Fun}
          {RS : RSym typD func}.

  Instance Expr_expr : @Expr typ typD (@expr typ func) :=
  { exprD' := fun tus tvs e t =>
                @exprD' typ typD _ _ _ _ nil tus tvs t e
  ; wf_Expr_acc := @wf_expr_acc typ func
  }.

  Instance ExprOk_expr (ts : list Type) : ExprOk Expr_expr.
  (** TODO(gmalecha): this proof should be here **)
  Admitted.

End Expr.