Require Import Coq.Lists.List.
Require Import ExtLib.Tactics.
Require Import MirrorCore.STac.Core.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Definition THEN (a b : stac typ expr subst) : stac typ expr subst :=
    fun tus tvs sub hs e =>
      let res := a tus tvs sub hs e in
      match res with
        | Solved tus tvs s => @Solved _ _ _ tus tvs s
        | More tus' tvs' sub hs e =>
          match b (tus ++ tus') (tvs ++ tvs') sub hs e with
            | Solved tus'' tvs'' sub =>
              @Solved _ _ _ (tus' ++ tus'') (tvs' ++ tvs'') sub
            | More tus'' tvs'' sub hs e =>
              More (tus' ++ tus'') (tvs' ++ tvs'') sub hs e
            | Fail => @Fail _ _ _
          end
        | Fail => res
      end.

  Variable RType_typ : RType typ.
  Variable Expr_expr : Expr RType_typ expr.
  Variable ExprOk_expr : ExprOk Expr_expr.
  Variable Typ0_Prop : Typ0 _ Prop.
  Variable Subst_subst : Subst subst expr.
  Variable SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst.

  Theorem THEN_sound
  : forall a b, stac_sound a -> stac_sound b -> stac_sound (THEN a b).
  Proof.
    intros; unfold stac_sound, THEN; intros.
    specialize (H tus tvs s hs g H1).
    destruct (a tus tvs s hs g); auto.
    destruct H.
    specialize (H0 (tus ++ l) (tvs ++ l0) s0 l1 e H).
    destruct (b (tus ++ l) (tvs ++ l0) s0 l1 e); auto.
    { forward_reason.
      split; auto.
      forward.
      rewrite substD_conv with (pfu := eq_sym (HList.app_ass_trans _ _ _))
                               (pfv := eq_sym (HList.app_ass_trans _ _ _)) in H4.
      unfold ResType in H4.
      autorewrite with eq_rw in H4.
      forward.
      inv_all; subst.
      eapply H5; clear H5.
      forward_reason.
      exists (fst (HList.hlist_split _ _ x)).
      simpl. intros.
      eapply H6; clear H6.
      exists (snd (HList.hlist_split _ _ x)).
      simpl. intros.
      autorewrite with eq_rw.
      specialize (H5 (HList.hlist_app vs' vs'0)); clear - H5.
      do 2 rewrite HList.hlist_app_assoc.
      rewrite HList.hlist_app_hlist_split.
      generalize dependent (HList.hlist_app us x).
      generalize dependent (HList.hlist_app vs (HList.hlist_app vs' vs'0)).
      clear.
      intros.
      match goal with
        | |- _ match eq_sym ?X with eq_refl => match ?Y with _ => _ end end
               match eq_sym ?A with eq_refl => match ?B with _ => _ end end =>
          change Y with X ; change B with A ; destruct A; destruct X
      end. assumption. }
    { forward_reason. split; auto.
      rewrite stateD_conv with (pfu := eq_sym (HList.app_ass_trans _ _ _))
                               (pfv := eq_sym (HList.app_ass_trans _ _ _)) in H3.
      unfold ResType in H3.
      autorewrite with eq_rw in H3.
      forward; inv_all; subst.
      eapply H5; clear H5.
      destruct H9.
      exists (fst (HList.hlist_split _ _ x)).
      intro.
      simpl. eapply H6; clear H6.
      exists (snd (HList.hlist_split _ _ x)).
      intros.
      do 2 rewrite HList.hlist_app_assoc.
      rewrite HList.hlist_app_hlist_split.
      specialize (H5 (HList.hlist_app vs' vs'0)).
      generalize dependent (HList.hlist_app us x).
      generalize dependent (HList.hlist_app vs (HList.hlist_app vs' vs'0)).
      intros.
      match goal with
        | |- match ?X with eq_refl => match ?Y with _ => _ end end
               match ?A with _ => _ end
               match ?B with _ => _ end =>
          change X with A ; change Y with B ; destruct A ; destruct B
      end; assumption. }
  Qed.

End parameterized.
