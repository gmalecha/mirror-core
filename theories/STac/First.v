Require Import Coq.Lists.List.
Require Import MirrorCore.STac.Core.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Definition FIRST (brs : list (stac typ expr subst)) : stac typ expr subst :=
    fun tus tvs sub e =>
      (fix FIRST (brs : list (stac typ expr subst)) : Result typ expr subst :=
         match brs with
           | nil => @Fail _ _ _
           | br :: brs =>
             match br tus tvs sub e with
               | Fail => FIRST brs
               | x => x
             end
         end) brs.

  Variable RType_typ : RType typ.
  Variable Expr_expr : Expr RType_typ expr.
  Variable ExprOk_expr : ExprOk Expr_expr.
  Variable Typ0_Prop : Typ0 _ Prop.
  Variable Subst_subst : Subst subst expr.
  Variable SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst.

  Theorem FIRST_sound
  : forall brs, Forall stac_sound brs ->
                stac_sound (FIRST brs).
  Proof.
    induction 1.
    { red. simpl. auto. }
    { red. simpl. intros.
      specialize (H tus tvs s g).
      destruct (x tus tvs s g); eauto.
      eapply IHForall. auto. }
  Qed.

End parameterized.
