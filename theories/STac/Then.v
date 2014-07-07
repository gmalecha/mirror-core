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
    fun tus tvs sub e =>
      let res := a tus tvs sub e in
      match res with
        | Solved tus tvs s => @Solved _ _ _ tus tvs s
        | More tus' tvs' sub e =>
          match b (tus ++ tus') (tvs ++ tvs') sub e with
            | Solved tus'' tvs'' sub => @Solved _ _ _ (tus' ++ tus'') (tvs' ++ tvs'') sub
            | More tus'' tvs'' sub e => More (tus' ++ tus'') (tvs' ++ tvs'') sub e
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
    unfold stac_sound, THEN; intros.
    specialize (H tus tvs s g).
    destruct (a tus tvs s g); auto.
    specialize (H0 (tus ++ l) (tvs ++ l0) s0 e).
    destruct (b (tus ++ l) (tvs ++ l0) s0 e); auto.
    { forward.
      match goal with
        | |- match ?X with _ => _ end =>
          consider X; intros
      end.
      { destruct H7 as [ ? [ ? ? ] ].
        eapply H4; clear H4.
        exists (fst (HList.hlist_split _ _ x)).
        exists (fst (HList.hlist_split _ _ x0)).
        eapply and_comm.
        eapply H5; clear H5.
        exists (snd (HList.hlist_split _ _ x)).
        exists (snd (HList.hlist_split _ _ x0)).
        do 2 rewrite HList.hlist_app_assoc.
        do 2 rewrite HList.hlist_app_hlist_split.
        repeat match goal with
                 | |- context [ match ?X with _ => _ end ] =>
                   destruct X
               end.
        rewrite H3 in *. inv_all; subst. assumption. }
      { intros. revert H3 H6.
        clear - P3. revert P3.
        do 2 rewrite app_ass. intros. congruence. } }
    { forward.
      repeat match goal with
               | |- match ?X with _ => _ end =>
                 consider X; intros
             end.
      { forward_reason.
        eapply H4; clear H4.
        exists (fst (HList.hlist_split _ _ x)).
        exists (fst (HList.hlist_split _ _ x0)).
        eapply and_comm.
        eapply H6; clear H6.
        exists (snd (HList.hlist_split _ _ x)).
        exists (snd (HList.hlist_split _ _ x0)).
        do 2 rewrite HList.hlist_app_assoc.
        do 2 rewrite HList.hlist_app_hlist_split.
        destruct (eq_sym (HList.app_ass_trans tus l l1)).
        destruct (eq_sym (HList.app_ass_trans tvs l0 l2)).
        rewrite H3 in *. rewrite H8 in *. inv_all; subst.
        split; assumption. }
      { revert H5 H8. clear. revert P4.
        do 2 rewrite app_ass. congruence. }
      { revert H7 H3. clear. revert P3.
        do 2 rewrite app_ass. congruence. } }
  Qed.

End parameterized.
