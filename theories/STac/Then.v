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
    intros.
    apply stac_sound_stac_sound_old in H.
    apply stac_sound_stac_sound_old in H0.
    apply stac_sound_stac_sound_old.
    unfold stac_sound_old, THEN in *; intros.
    specialize (H tus tvs s hs g).
    destruct (a tus tvs s hs g); auto.
    specialize (H0 (tus ++ l) (tvs ++ l0) s0 l1 e).
    destruct (b (tus ++ l) (tvs ++ l0) s0 l1 e); auto.
    { forward_reason. split; auto.
      forward.
      match goal with
        | |- match ?X with _ => _ end =>
          consider X; intros
      end.
      { forward_reason.
        eapply H9; clear H9; eauto.
        exists (fst (HList.hlist_split _ _ x)).
        exists (fst (HList.hlist_split _ _ x0)).
        intro.
        eapply and_comm.
        eapply H10; clear H10; eauto.
        exists (snd (HList.hlist_split _ _ x)).
        exists (snd (HList.hlist_split _ _ x0)).
        do 2 rewrite HList.hlist_app_assoc.
        do 2 rewrite HList.hlist_app_hlist_split.
        repeat match goal with
                 | |- context [ match ?X with _ => _ end ] =>
                   destruct X
               end.
        rewrite H8 in *. inv_all; subst. assumption. }
      { intros. revert H11 H8.
        clear - P3. revert P3.
        do 2 rewrite app_ass. intros. congruence. } }
    { forward_reason. split; auto.
      forward.
      repeat match goal with
               | |- match ?X with _ => _ end =>
                 consider X; intros
             end.
      { forward_reason.
        eapply H9; clear H9; auto.
        exists (fst (HList.hlist_split _ _ x)).
        exists (fst (HList.hlist_split _ _ x0)).
        intro.
        eapply and_comm.
        eapply H12; clear H12; eauto.
        exists (snd (HList.hlist_split _ _ x)).
        exists (snd (HList.hlist_split _ _ x0)).
        do 2 rewrite HList.hlist_app_assoc.
        do 2 rewrite HList.hlist_app_hlist_split.
        destruct (eq_sym (HList.app_ass_trans tus l l2)).
        destruct (eq_sym (HList.app_ass_trans tvs l0 l3)).
        repeat match goal with
                 | H : _ = _ , H' : _ = _ |- _ =>
                   rewrite H in H'
               end.
        inv_all; subst. auto. }
      { revert H11 H15. clear. revert P4.
        do 2 rewrite app_ass. congruence. }
      { revert H10 H14. clear. revert l7.
        do 2 rewrite app_ass. congruence. }
      { revert H13 H8. clear. revert P3.
        do 2 rewrite app_ass. congruence. } }
  Qed.

End parameterized.
