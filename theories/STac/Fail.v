Require Import MirrorCore.STac.Core.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Definition FAIL : stac typ expr subst :=
    fun _ _ _ _ _ =>
      @Fail _ _ _.

  Variable RType_typ : RType typ.
  Variable Expr_expr : Expr RType_typ expr.
  Variable Typ0_Prop : Typ0 _ Prop.
  Variable Subst_subst : Subst subst expr.
  Variable SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst.

  Theorem FAIL_sound : stac_sound FAIL.
  Proof.
    red. simpl. auto.
  Qed.

End parameterized.

Arguments FAIL {_ _ _} _ _ _ _ _.