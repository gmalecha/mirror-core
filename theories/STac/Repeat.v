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
           fun tus tvs sub e =>
             (** This is like THEN, but lazier **)
             match br tus tvs sub e with
               | Fail => More nil nil sub e (** Never fails **)
               | More tus' tvs' sub e =>
                 match DO n (tus ++ tus') (tvs ++ tvs') sub e with
                   | More tus'' tvs'' sub e =>
                     More (tus' ++ tus'') (tvs' ++ tvs'') sub e
                   | Solved tus'' tvs'' sub =>
                     @Solved _ _ _ (tus' ++ tus'') (tvs' ++ tvs'') sub
                   | Fail => More tus' tvs' sub e
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
    { red; intros. eapply IDTAC_sound. }
    { red. intros.
      specialize (H tus tvs s g).
      destruct (br tus tvs s g); auto.
      { eapply More_sound. }
      { specialize (IHn (tus ++ l) (tvs ++ l0) s0 e).
        destruct (REPEAT n br (tus ++ l) (tvs ++ l0) s0 e); auto.
        { forward.
          match goal with
            | |- match ?X with _ => _ end =>
              consider X; intros
          end.
          { destruct H6 as [ ? [ ? ? ] ].
            eapply H3; clear H3.
            exists (fst (HList.hlist_split _ _ x)).
            exists (fst (HList.hlist_split _ _ x0)).
            apply and_comm.
            apply IHn; clear IHn.
            exists (snd (HList.hlist_split _ _ x)).
            exists (snd (HList.hlist_split _ _ x0)).
            do 2 rewrite hlist_app_assoc.
            do 2 rewrite hlist_app_hlist_split.
            destruct (eq_sym (app_ass_trans tus l l1)).
            destruct (eq_sym (app_ass_trans tvs l0 l2)).
            rewrite H4 in *. inv_all; subst. assumption. }
        { clear - H4 H5.
          generalize dependent P3.
          do 2 rewrite app_ass. intros. congruence. } }
        { forward.
          repeat match goal with
                   | |- match ?X with _ => _ end =>
                     consider X; intros
                 end.
          { destruct H8 as [ ? [ ? ? ] ].
            eapply H3; clear H3.
            exists (fst (HList.hlist_split _ _ x)).
            exists (fst (HList.hlist_split _ _ x0)).
            apply and_comm.
            apply IHn; clear IHn.
            exists (snd (HList.hlist_split _ _ x)).
            exists (snd (HList.hlist_split _ _ x0)).
            do 2 rewrite hlist_app_assoc.
            do 2 rewrite hlist_app_hlist_split.
            destruct (eq_sym (app_ass_trans tus l l1)).
            destruct (eq_sym (app_ass_trans tvs l0 l2)).
            rewrite H4 in *. rewrite H5 in *.
            inv_all. subst; tauto. }
          { revert H7 H5.
            clear. revert P4. do 2 rewrite app_ass. congruence. }
          { revert H4 H6. clear. revert P3.
            do 2 rewrite app_ass. congruence. } } } }
  Qed.

End parameterized.
