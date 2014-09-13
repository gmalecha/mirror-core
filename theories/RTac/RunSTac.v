Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.STac.Core.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.Reduce.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Context {typ : Type}.
  Context {expr : Type}.
  Context {subst : Type}.
  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Subst_subst : Subst subst expr}.
  Context {SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst}.
  Context {SubstUpdate_subst : SubstUpdate subst expr}.

  Variable instantiate : (nat -> option expr) -> nat -> expr -> expr.

  Definition STAC_no_hyps (tac : stac typ expr subst)
  : rtac typ expr subst :=
    fun ctx sub gl =>
      let '(tus,tvs) := getEnvs ctx in
      match tac tus tvs sub nil gl with
        | STac.Core.Fail => Fail
        | STac.Core.More tus' tvs' sub' hs' gl' =>
          reduceGoal instantiate
                     (List.fold_right (fun x y => @CEx _ _ y x)
                         (List.fold_right (fun x y => @CAll _ _ y x)
                            CTop tvs') tus') sub' (GGoal gl') (length tus + length tus') (length tvs + length tvs')
        | STac.Core.Solved tus' tvs' sub' =>
          reduceGoal instantiate
                     (List.fold_right (fun x y => @CEx _ _ y x)
                       (List.fold_right (fun x y => @CAll _ _ y x)
                          CTop tvs') tus') sub' GSolved (length tus + length tus') (length tvs + length tvs')
      end.

(*
  Lemma goalD_fold_right_GExs
  : forall tvs g ls tus,
      match goalD tus tvs (fold_right (@GExs _ _ _) g ls)
          , goalD (tus ++ ls) tvs g
      with
        | Some D , Some D' =>
          forall us vs,
            D us vs <->
            _exists
              (fun us' : HList.hlist typD ls =>
                 D' (HList.hlist_app us us') vs)
        | None , None => True
        | _ , _ => False
      end.
  Proof.
    clear.
    induction ls; simpl.
    { intros.
      rewrite goalD_conv
      with (pfu := eq_sym (HList.app_nil_r_trans _)) (pfv := eq_refl).
      autorewrite with eq_rw.
      destruct (goalD tus tvs g); auto.
      intros. rewrite HList.hlist_app_nil_r.
      clear.
      match goal with
        | |- _ <-> (match ?X with _ => _ end
                      match ?Y with _ => _ end _) =>
          change Y with X ; destruct X
      end.
      reflexivity. }
    { intros.
      specialize (IHls (tus ++ a :: nil)).
      rewrite goalD_conv
      with (pfu := eq_sym (HList.app_ass_trans _ _ _)) (pfv := eq_refl)
        in IHls.
      autorewrite with eq_rw in IHls. simpl in *.
      destruct (goalD (tus ++ a :: nil) tvs (fold_right GExs g ls));
        destruct (goalD (tus ++ a :: ls) tvs g); auto.
      intros.
      eapply exists_iff; intro.
      etransitivity. eapply IHls.
      eapply _exists_iff; intro.
      autorewrite with eq_rw.
      match goal with
        | |- ?X <-> ?Y =>
          cutrewrite (X = Y); try reflexivity
      end.
      f_equal.
      clear.
      change (HList.Hcons x x0)
      with (HList.hlist_app (HList.Hcons x HList.Hnil) x0).
      rewrite HList.hlist_app_assoc.
      simpl.
      apply Eq.match_eq_sym_eq'. }
  Qed.

  Lemma goalD_fold_right_GAlls
  : forall tus g ls tvs,
      match goalD tus tvs (fold_right GAlls g ls)
          , goalD tus (tvs ++ ls) g
      with
        | Some D , Some D' =>
          forall us vs,
            D us vs <->
            _foralls
              (fun vs' : HList.hlist typD ls =>
                 D' us (HList.hlist_app vs vs'))
        | None , None => True
        | _ , _ => False
      end.
  Proof.
    clear.
    induction ls; simpl.
    { intros.
      rewrite goalD_conv
      with (pfu := eq_refl) (pfv := eq_sym (HList.app_nil_r_trans _)).
      autorewrite with eq_rw.
      destruct (goalD tus tvs g); auto.
      intros. rewrite HList.hlist_app_nil_r.
      clear.
      match goal with
        | |- _ <-> (match ?X with _ => _ end
                      _ match ?Y with _ => _ end) =>
          change Y with X ; destruct X
      end.
      reflexivity. }
    { intros.
      specialize (IHls (tvs ++ a :: nil)).
      rewrite goalD_conv
      with (pfu := eq_refl) (pfv := eq_sym (HList.app_ass_trans _ _ _))
        in IHls.
      autorewrite with eq_rw in IHls. simpl in *.
      destruct (goalD tus (tvs ++ a :: nil) (fold_right GAlls g ls));
        destruct (goalD tus (tvs ++ a :: ls) g); auto.
      intros.
      eapply forall_iff; intro.
      etransitivity. eapply IHls.
      eapply _forall_iff; intro.
      autorewrite with eq_rw.
      match goal with
        | |- ?X <-> ?Y =>
          cutrewrite (X = Y); try reflexivity
      end.
      f_equal.
      clear.
      change (HList.Hcons x x0)
      with (HList.hlist_app (HList.Hcons x HList.Hnil) x0).
      rewrite HList.hlist_app_assoc.
      simpl.
      apply Eq.match_eq_sym_eq'. }
  Qed.

  Lemma _exists_sem : forall ls P,
                        _exists (ls := ls) P <->
                        exists x, P x.
  Proof.
    clear. induction ls; simpl; auto.
    - intuition. exists HList.Hnil. auto.
      destruct H. rewrite (HList.hlist_eta x) in H.
      assumption.
    - intros. split.
      + destruct 1.
        eapply IHls in H.
        destruct H. eauto.
      + destruct 1.
        exists (HList.hlist_hd x).
        eapply IHls.
        exists (HList.hlist_tl x).
        rewrite (HList.hlist_eta x) in H.
        assumption.
  Qed.
  Lemma _forall_sem : forall ls P,
                        _foralls (ls := ls) P <->
                        forall x, P x.
  Proof.
    clear. induction ls; simpl; auto.
    - intuition. rewrite (HList.hlist_eta x).
      assumption.
    - intros. split.
      + intros.
        rewrite (HList.hlist_eta x).
        eapply IHls in H.
        eapply H.
      + intros.
        eapply IHls.
        intros. eapply H.
  Qed.

  Lemma at_bottom_WF_option
  : forall f,
      (forall a b c d g,
         f a b c d = Some g ->
         WellFormed_subst c ->
         WellFormed_goal g) ->
    forall g tus tvs g',
      at_bottom f tus tvs g = Some g' ->
      WellFormed_goal g ->
      WellFormed_goal g'.
  Proof.
    clear.
    induction g; simpl; intros; forwardy; inv_all; subst; simpl in *; eauto.
  Qed.

  Lemma WellFormed_goal_GAlls
  : forall ls g,
      WellFormed_goal g <-> WellFormed_goal (fold_right GAlls g ls).
  Proof.
    clear. induction ls; simpl; intros; auto.
    reflexivity.
  Qed.
  Lemma WellFormed_goal_GExs
  : forall ls g,
      WellFormed_goal g <-> WellFormed_goal (fold_right GExs g ls).
  Proof.
    clear. induction ls; simpl; intros; auto.
    reflexivity.
  Qed.
  Lemma WellFormed_goal_GHyps
  : forall ls g,
      WellFormed_goal g <-> WellFormed_goal (fold_right GHyps g ls).
  Proof.
    clear. induction ls; simpl; intros; auto.
    reflexivity.
  Qed.


  Theorem STAC_no_hyps_sound
  : forall tac, stac_sound tac ->
                rtac_sound nil nil (STAC_no_hyps tac).
  Proof.
(*
    intros.
    unfold rtac_sound, STAC_no_hyps.
    intros. split.
    { eapply at_bottom_WF_option in H0; auto.
      destruct d.
      + intros. specialize (H a b c nil e H3).
        destruct (tac a b c nil e); try congruence.
        - destruct H. clear - H H2.
          inversion H2.
          apply WellFormed_goal_GExs.
          apply WellFormed_goal_GAlls.
          simpl. assumption.
        - destruct H; clear - H H2.
          inversion H2.
          apply WellFormed_goal_GExs.
          apply WellFormed_goal_GAlls.
          apply WellFormed_goal_GHyps.
          simpl. assumption.
      + clear. inversion 1.
        refine (fun x => x). }
    eapply at_bottom_sound_option in H0; eauto; clear H0.
    simpl.
    intros.
    destruct e.
    { assert (WellFormed_subst s) by admit.
      consider (tac tus' tvs' s nil e); try congruence;
      intros; inv_all; subst.
      { specialize (H tus' tvs' s nil e H1).
        rewrite H0 in H; clear H0 H1.
        forward_reason.
        unfold stateD in *.
        unfold propD, Core.propD in *.
        forward.
        simpl in H2.
        forwardy.
        specialize (goalD_fold_right_GExs tvs'
                      (fold_right GAlls (GGoal s0 None) l0)
                      l tus').
        match goal with
          | |- match ?X with _ => _ end ->
               match ?Y with _ => _ end =>
            change Y with X ; destruct X
        end;
        specialize (goalD_fold_right_GAlls (tus' ++ l)
                      (GGoal s0 None)
                      l0 tvs');
        match goal with
          | |- match ?X with _ => _ end ->
               match ?Y with _ => _ end -> _ =>
            change Y with X ; destruct X
        end; auto.
        { simpl. intros; forwardy.
          inv_all; subst.
          eapply H3; auto; clear H3.
          eapply H5 in H6; clear H5.
          eapply _exists_sem in H6.
          destruct H6.
          exists x.
          intros.
          change_rewrite H2 in H4.
          inv_all; subst.
          eapply H7 in H3; clear H7.
          eapply _forall_sem in H3. eapply H3. }
        { inversion 2. }
        { simpl. rewrite H2. auto. } }
      { specialize (H tus' tvs' s nil e H1).
        rewrite H0 in H.
        

 } }
    { inv_all; subst.
      simpl. forward. }
*)
  Abort.
*)

End parameterized.
