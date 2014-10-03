Require Import Coq.Lists.List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.
Require Import MirrorCore.STac.Core.
Require Import MirrorCore.STac.Idtac.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Definition REPEAT (max : nat) (br : stac typ expr subst)
  : stac typ expr  subst :=
    (fix DO (n : nat) : stac typ expr  subst :=
       match n with
         | 0 => @IDTAC _ _ _
         | S n =>
           fun tus tvs sub hs e =>
             (** This is like THEN, but lazier **)
             match br tus tvs sub hs e with
               | Fail => More nil nil sub hs e (** Never fails **)
               | More tus' tvs' sub hs e =>
                 match DO n (tus ++ tus') (tvs ++ tvs') sub hs e with
                   | More tus'' tvs'' sub hs' e =>
                     More (tus' ++ tus'') (tvs' ++ tvs'') sub hs' e
                   | Solved tus'' tvs'' sub =>
                     @Solved _ _ _ (tus' ++ tus'') (tvs' ++ tvs'') sub
                   | Fail => More tus' tvs' sub hs e
                 end
               | Solved tus tvs s => @Solved _ _ _ tus tvs s
             end
       end) max.

  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Subst_subst : Subst subst expr}.
  Context {SubstOk_subst : SubstOk Subst_subst}.

  Theorem REPEAT_sound
  : forall br, stac_sound br ->
               forall n,
                 stac_sound (REPEAT n br).
  Proof.
    induction n; simpl.
    { red; intros. eapply IDTAC_sound; auto. }
    { red. intros. unfold stateD in *.
      specialize (H tus tvs s hs g).
      destruct (br tus tvs s hs g); auto.
      { split; auto. eapply More_sound. }
      { specialize (IHn (tus ++ l) (tvs ++ l0) s0 l1 e).
        destruct (REPEAT n br (tus ++ l) (tvs ++ l0) s0 l1 e); auto.
        { forward_reason. split; auto.
          unfold stateD in *.
          forward. inv_all; subst.
          match goal with
            | |- match ?X with _ => _ end =>
              consider X; intros
          end.
          { forward_reason. intros.
            inv_all; subst.
            eapply H5; auto; clear H5.
            exists (fst (HList.hlist_split _ _ x)).
            intros.
            eapply H6; clear H6; auto.
            exists (snd (HList.hlist_split _ _ x)).
            intros.
            do 2 rewrite hlist_app_assoc.
            rewrite hlist_app_hlist_split.
            rewrite substD_conv
               with (pfu := app_ass_trans tus l l2)
                    (pfv := app_ass_trans tvs l0 l3)
              in H9.
            rewrite H4 in H9.
            autorewrite with eq_rw in H9.
            inv_all; subst.
            clear - H12.
            specialize (H12 (hlist_app vs' vs'0)).
            generalize dependent (hlist_app us x).
            generalize dependent (hlist_app vs (hlist_app vs' vs'0)).
            clear.
            destruct (app_ass_trans tus l l2); auto. }
        { clear - H4 H9.
          generalize dependent e2.
          do 2 rewrite app_ass. intros. congruence. } }
        { forward_reason. split; auto. unfold stateD in *.
          forward.
          repeat match goal with
                   | |- match ?X with _ => _ end =>
                     consider X; intros
                 end.
          { inv_all; subst.
            eapply H5; auto; clear H5.
            forward_reason.
            exists (fst (HList.hlist_split _ _ x)).
            intro. apply H6; clear H6; auto.
            exists (snd (HList.hlist_split _ _ x)).
            intro.
            do 2 rewrite hlist_app_assoc.
            rewrite hlist_app_hlist_split.
            rewrite substD_conv
               with (pfu := eq_sym (app_ass_trans _ _ _))
                    (pfv := eq_sym (app_ass_trans _ _ _)) in H8.
            unfold propD in *.
            rewrite ExprDAs.exprD'_typ0_conv
               with (pfu := eq_sym (app_ass_trans _ _ _))
                    (pfv := eq_sym (app_ass_trans _ _ _)) in H4.
            rewrite ExprDAs.exprD'_typ0_conv
               with (pfu := eq_sym (app_ass_trans _ _ _))
                    (pfv := eq_sym (app_ass_trans _ _ _)) in H7.
            autorewrite with eq_rw in *.
            forward; inv_all; subst.
            autorewrite with eq_rw.
            eapply H5; clear H5.
            destruct (eq_sym (app_ass_trans tus l l2)).
            destruct (eq_sym (app_ass_trans tvs l0 l3)).
            rewrite H7 in H12; clear H7.
            inv_all; subst; assumption. }
          { revert H16.
            clear - H7 H8 H4.
            rewrite propD_conv
               with (pfu := app_ass_trans tus l l2)
                    (pfv := app_ass_trans tvs l0 l3).
            rewrite substD_conv
               with (pfu := app_ass_trans tus l l2)
                    (pfv := app_ass_trans tvs l0 l3).
            rewrite H8.
            autorewrite with eq_rw.
            rewrite H4.
            destruct (app_ass_trans tus l l2).
            destruct (app_ass_trans tvs l0 l3).
            rewrite H7. congruence. } } } }
  Qed.

End parameterized.
