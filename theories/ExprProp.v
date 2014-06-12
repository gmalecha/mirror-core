Require Import Coq.Lists.List.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.

Set Implicit Arguments.
Set Strict Implicit.

Section semantic.
  Context {RType_typ : RType}.
  Variable TI_prop : Typ0 _ Prop.
  Variable expr : Type.
  Context {Expr_expr : Expr _ expr}.

  Let tvProp := @typ0 _ _ TI_prop.

  Definition Provable_val (val : typD nil tvProp) : Prop :=
    match typ0_cast nil in _ = t return t with
      | eq_refl => val
    end.

  Definition Provable uvars vars (e : expr) : Prop :=
    match exprD uvars vars e tvProp with
      | None => False
      | Some p => Provable_val p
    end.

  Definition AllProvable uvars vars (es : list expr) :=
    Forall (Provable uvars vars) es.

End semantic.
