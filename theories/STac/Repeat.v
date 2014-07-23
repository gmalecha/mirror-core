Require Import Coq.Lists.List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.SubstI3.
Require Import MirrorCore.Util.Iteration.
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

  Variable RType_typ : RType typ.
  Variable Expr_expr : Expr RType_typ expr.
  Variable Typ0_Prop : Typ0 _ Prop.
  Variable Subst_subst : Subst subst expr.
  Variable SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst.

  Theorem REPEAT_sound
  : forall br, stac_sound br ->
               forall n,
                 stac_sound (REPEAT n br).
  Proof.
    induction n; simpl.
    { red; intros. eapply IDTAC_sound; auto. }
    { red. intros.
      specialize (H tus tvs s hs g).
      destruct (br tus tvs s hs g); auto.
      { split; auto. eapply More_sound. }
      { specialize (IHn (tus ++ l) (tvs ++ l0) s0 l1 e).
        destruct (REPEAT n br (tus ++ l) (tvs ++ l0) s0 l1 e); auto.
        { forward_reason. split; auto.
          forward.
          match goal with
            | |- match ?X with _ => _ end =>
              consider X; intros
          end.
          { destruct H12 as [ ? [ ? ? ] ].
            eapply H9; auto; clear H9.
            exists (fst (HList.hlist_split _ _ x)).
            exists (fst (HList.hlist_split _ _ x0)).
            simpl. intro.
            apply and_comm.
            apply H10; auto; clear H10.
            exists (snd (HList.hlist_split _ _ x)).
            exists (snd (HList.hlist_split _ _ x0)).
            do 2 rewrite hlist_app_assoc.
            do 2 rewrite hlist_app_hlist_split.
            destruct (eq_sym (app_ass_trans tus l l2)).
            destruct (eq_sym (app_ass_trans tvs l0 l3)).
            rewrite H8 in *. inv_all; subst. assumption. }
        { clear - H8 H11.
          generalize dependent P3.
          do 2 rewrite app_ass. intros. congruence. } }
        { forward_reason. split; auto.
          forward.
          repeat match goal with
                   | |- match ?X with _ => _ end =>
                     consider X; intros
                 end.
          { destruct H16 as [ ? [ ? ? ] ].
            eapply H9; auto; clear H9.
            exists (fst (HList.hlist_split _ _ x)).
            exists (fst (HList.hlist_split _ _ x0)).
            simpl. intro.
            apply and_comm.
            apply H12; auto; clear H12.
            exists (snd (HList.hlist_split _ _ x)).
            exists (snd (HList.hlist_split _ _ x0)).
            do 2 rewrite hlist_app_assoc.
            do 2 rewrite hlist_app_hlist_split.
            destruct (eq_sym (app_ass_trans tus l l2)).
            destruct (eq_sym (app_ass_trans tvs l0 l3)).
            rewrite H10 in *. rewrite H11 in *. rewrite H13 in *.
            inv_all. subst; tauto. }
          { clear - H15 H11.
            generalize dependent P4.
            do 2 rewrite app_ass. congruence. }
          { clear - H14 H10.
            generalize dependent l7.
            do 2 rewrite app_ass. congruence. }
          { clear - H13 H8.
            generalize dependent P3.
            do 2 rewrite app_ass. congruence. } } } }
  Qed.

End parameterized.
