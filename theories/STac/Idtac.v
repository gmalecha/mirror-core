Require Import MirrorCore.STac.Core.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Definition IDTAC : stac typ expr subst :=
    fun _ _ sub e => @More _ _ _ nil nil sub e.

  Variable RType_typ : RType typ.
  Variable Expr_expr : Expr RType_typ expr.
  Variable Typ0_Prop : Typ0 _ Prop.
  Variable Subst_subst : Subst subst expr.
  Variable SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst.

  Theorem IDTAC_sound : stac_sound IDTAC.
  Proof.
    intros. unfold IDTAC. red. intros. split; auto. eapply More_sound.
  Qed.

End parameterized.
