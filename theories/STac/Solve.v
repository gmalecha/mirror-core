Require Import MirrorCore.STac.Core.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Definition SOLVE (b : stac typ expr subst) : stac typ expr subst :=
    fun e sub tus tvs =>
      match b e sub tus tvs with
        | Solved tus tvs s => @Solved _ _ _ tus tvs s
        | x => @Fail _ _ _
      end.

  Variable RType_typ : RType typ.
  Variable Expr_expr : Expr RType_typ expr.
  Variable ExprOk_expr : ExprOk Expr_expr.
  Variable Typ0_Prop : Typ0 _ Prop.
  Variable Subst_subst : Subst subst expr.
  Variable SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst.

  Theorem SOLVE_sound : forall t, stac_sound t -> stac_sound (SOLVE t).
  Proof.
    unfold stac_sound; simpl; intros.
    red. specialize (H tus tvs s g).
    destruct (t tus tvs s g); auto.
  Qed.

End parameterized.
