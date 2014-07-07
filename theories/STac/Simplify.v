Require Import ExtLib.Tactics.
Require Import MirrorCore.STac.Core.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Definition SIMPLIFY
             (f : list typ -> list typ -> subst -> expr -> expr)
  : stac typ expr subst :=
    fun tus tvs s e =>
      More nil nil s (f tus tvs s e).

  Variable RType_typ : RType typ.
  Variable Expr_expr : Expr RType_typ expr.
  Variable ExprOk_expr : ExprOk Expr_expr.
  Variable Typ0_Prop : Typ0 _ Prop.
  Variable Subst_subst : Subst subst expr.
  Variable SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst.

  Theorem SIMPLIFY_sound
  : forall f,
      (forall tus tvs s e e',
         f tus tvs s e = e' ->
         match @goalD _ _ _ Expr_expr _ tus tvs e
             , @substD _ _ _ _ Expr_expr _ _ tus tvs s
             , @goalD _ _ _ _ _ tus tvs e'
         with
           | None , _ , _ => True
           | _ , None , _ => True
           | Some _ , Some _ , None => False
           | Some eD , Some sD , Some eD' =>
             forall us vs,
               sD us vs ->
               eD us vs <-> eD' us vs
         end) ->
      stac_sound (SIMPLIFY f).
  Proof.
    intros. unfold stac_sound, SIMPLIFY.
    intros.
    specialize (H tus tvs s g _ eq_refl).
    forward.
    repeat match goal with
             | |- match ?X with _ => _ end =>
               consider X; intros
           end.
    { destruct H5 as [ ? [ ? ? ] ].
      rewrite (HList.hlist_eta x) in *.
      rewrite (HList.hlist_eta x0) in *.
      do 2 rewrite HList.hlist_app_nil_r in H5.
      specialize (H2 us vs).
      destruct (eq_sym (HList.app_nil_r_trans tus)).
      destruct (eq_sym (HList.app_nil_r_trans tvs)).
      rewrite H4 in *.
      rewrite H3 in *. inv_all; subst.
      intuition. }
    { clear - H4 H0.
      do 2 rewrite List.app_nil_r in *. congruence. }
    { clear - H3 H1.
      do 2 rewrite List.app_nil_r in *. congruence. }
  Qed.

End parameterized.
