Require Import Compare_dec.
Require Import ExtLib.Data.Pair.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SymI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.ExprLift.

(** TODO **)
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Set Strict Implicit.

Section app_full.
  Variable ts : types.
  Variable sym : Type.
  Variable RSym_sym : RSym (typD ts) sym.

  Fixpoint apps (e : expr sym) (ls : list (expr sym)) :=
    match ls with
      | nil => e
      | l :: ls => apps (App e l) ls
    end.

  Fixpoint app_full' (e : expr sym) (acc : list (expr sym)) : expr sym * list (expr sym) :=
    match e with
      | App l r =>
        app_full' l (r :: acc)
      | _ =>
        (e, acc)
    end.

  Definition app_full (e : expr sym) := app_full' e nil.

  Lemma apps_app_full'
  : forall e e' ls ls',
      app_full' e ls = (e', ls') ->
      apps e ls = apps e' ls'.
  Proof.
    induction e; simpl; intros; inv_all; subst; auto.
    eapply IHe1 in H. auto.
  Qed.
End app_full.

Section substitute.
  Variable ts : types.
  Variable sym : Type.
  Variable RSym_sym : RSym (typD ts) sym.

  Fixpoint substitute' (v : var) (w : expr sym) (e : expr sym) : expr sym :=
    match e with
      | Var v' =>
        match nat_compare v v' with
          | Eq => w
          | Lt => Var (v' - 1)
          | Gt => Var v'
        end
      | UVar u => UVar u
      | Inj i => Inj i
      | App l' r' => App (substitute' v w l') (substitute' v w r')
      | Abs t e => Abs t (substitute' (S v) (lift 0 1 w) e)
    end.

  Lemma substitute'_lem
  : forall e tvs w e',
      substitute' (length tvs) w e = e' ->
      forall tus tvs' t t',
        typeof_expr tus (tvs ++ tvs') w = Some t ->
        typeof_expr tus (tvs ++ t :: tvs') e = Some t' ->
        typeof_expr tus (tvs ++ tvs') e' = Some t' /\
        (forall (us : hlist _ tus) val x,
           exprD' (join_env us) (tvs ++ tvs') w t = Some val ->
           exprD' (join_env us) (tvs ++ t :: tvs') e t' = Some x ->
           match
             exprD' (join_env us) (tvs ++ tvs') e' t'
           with
             | None => False
             | Some val' =>
               forall (gs : hlist (typD ts nil) tvs) (gs' : hlist (typD ts nil) tvs'),
                 x (hlist_app gs (Hcons (val (hlist_app gs gs')) gs')) =
                 val' (hlist_app gs gs')
           end).
  Proof.
    induction e; simpl; intros; subst.
    { destruct (nat_compare_spec (length tvs) v).
      { subst.
        rewrite nth_error_app_R in H1 by omega.
        rewrite Minus.minus_diag in *. simpl in H1; inversion H1; clear H1; subst.
        split; auto.
        intros. rewrite H. intuition.
        specialize (@exprD'_Var_App_R _ _ RSym_sym (join_env us) (t' :: tvs') t' tvs (length tvs)).
        rewrite H1. rewrite Minus.minus_diag.
        rewrite exprD'_Var. simpl.
        rewrite typ_cast_typ_refl; intros.
        eapply H2. omega. }
      { simpl.
        repeat rewrite nth_error_app_R in * by omega.
        replace (v - length tvs) with (S (v - 1 - length tvs)) in H1 by omega.
        simpl in H1. split; auto.
        intros.
        assert (v >= length tvs) by omega.
        specialize (@exprD'_Var_App_R _ _ RSym_sym (join_env us) (t :: tvs') t' tvs v H4); clear H4.
        rewrite H3. intro.
        assert (v - 1 >= length tvs) by omega.
        specialize (@exprD'_Var_App_R _ _ RSym_sym (join_env us) tvs' t' tvs (v - 1) H5); clear H5; simpl.
        simpl in *; intros.
        assert (v - length tvs >= 1) by omega.
        specialize (@exprD'_Var_App_R _ _ RSym_sym (join_env us) tvs' t' (t :: nil) (v - length tvs) H6); clear H6; simpl.
        intros.
        replace (v - length tvs - 1) with (v - 1 - length tvs) in * by omega.
        repeat match goal with
                 | H : context [ match ?X with _ => _ end ] |- _ =>
                   consider X; intros
                 | H : forall x : hlist _ _, _ , H' : _ |- _ =>
                   specialize (H H')
              end; intuition.
        { specialize (H8 (Hcons (val (hlist_app gs gs')) Hnil) gs').
          specialize (H6 (Hcons (val (hlist_app gs gs')) gs')).
          simpl in *.
          etransitivity. eapply H6. etransitivity. eapply H8.
          eauto. } }
      { simpl. repeat rewrite nth_error_app_L in * by omega.
        split; auto; intros.
        specialize (@exprD'_Var_App_L _ _ RSym_sym (join_env us) (t :: tvs') t' tvs v H).
        specialize (@exprD'_Var_App_L _ _ RSym_sym (join_env us) tvs' t' tvs v H).
        intros.
        repeat match goal with
                 | H : context [ match ?X with _ => _ end ] |- _ =>
                   consider X; intros
                 | H : forall x : hlist _ _, _ , H' : _ |- _ =>
                   specialize (H H')
              end; intuition try congruence.
        { inv_all; subst.
          specialize (H7 (Hcons (val (hlist_app gs gs')) gs')).
          simpl in *. etransitivity. eapply H7. eauto. } } }
    { simpl; split; auto; intros.
      red_exprD.
      forward. inv_all; subst; auto. }
    { simpl. forward.
      specialize (IHe1 tvs w _ eq_refl tus tvs' _ _ H0 H).
      specialize (IHe2 tvs w _ eq_refl tus tvs' _ _ H0 H1).
      destruct IHe1; destruct IHe2.
      rewrite H3 in *. rewrite H5 in *.
      intuition.
      red_exprD. Cases.rewrite_all.
      unfold type_of_apply in *; forward. inv_all.
      revert H13. subst; intros; subst.
      rewrite exprD'_type_cast in H11.
      rewrite typeof_env_join_env in *.
      rewrite H1 in *. forward.
      inv_all; subst.
      specialize (H6 _ _ _ H7 H8).
      specialize (H4 _ _ _ H7 H10).
      forward. rewrite typ_cast_typ_refl.
      intuition. rewrite H4. rewrite H6. reflexivity. }
    { simpl in *. forward.
      inv_all; subst.
      specialize (fun x => IHe (t :: tvs) (lift 0 1 w) _ eq_refl tus tvs' t0 t1 x H).
      destruct IHe.
      { generalize (typeof_expr_lift RSym_sym tus nil (t :: nil) (tvs ++ tvs') w).
        simpl. congruence. }
      { simpl in *. rewrite H1. intuition.
        red_exprD.
        forward. inv_all; subst.
        generalize (exprD'_lift RSym_sym (join_env us) nil (t :: nil) (tvs ++ tvs') w t0); simpl; intros.
        specialize (H2 us).
        destruct (exprD' (join_env us) (t :: tvs ++ tvs') (lift' 0 1 w) t0).
        { forward; inv_all; subst.
          specialize (@H2 _ _ eq_refl H4).
          forward.
          eapply functional_extensionality. intros.
          specialize (H5 (Hcons x gs) gs').
          specialize (H6 Hnil (Hcons x Hnil) (hlist_app gs gs')).
          simpl in *.
          etransitivity. 2: eapply H5.
          f_equal. f_equal. f_equal. f_equal. auto. }
        { forward. } } }
    { simpl. intuition.
      red_exprD. forward; inv_all; subst. auto. }
  Qed.

  Theorem substitute'_typed
  : forall e tvs w tus tvs' t t',
      typeof_expr tus (tvs ++ tvs') w = Some t ->
      typeof_expr tus (tvs ++ t :: tvs') e = Some t' ->
      typeof_expr tus (tvs ++ tvs') (substitute' (length tvs) w e) = Some t'.
  Proof.
    intros. eapply substitute'_lem; eauto.
  Qed.

  Lemma split_env_typeof_env
  : forall us x h,
      split_env (typD := typD ts) us = existT _ x h ->
      x = typeof_env us /\ join_env h = us.
  Proof.
    clear; intros.
    unfold typeof_env.
    rewrite <- split_env_projT1.
    rewrite H. split; auto.
    match goal with
      | H : _ = ?X |- join_env ?Y = _ =>
        change Y with (projT2 X)
    end.
    generalize dependent x. induction us; simpl; intros.
    { inversion H. simpl; auto. }
    { inv_all. subst. subst. simpl. f_equal.
      { destruct a; auto. }
      { destruct (split_env us).
        specialize (IHus _ _ eq_refl). auto. } }
  Qed.

  Theorem substitute'_exprD
  : forall e vs w us vs' t t' v val,
      exprD us (vs ++ vs') w t = Some v ->
      exprD us (vs ++ (@existT _ _ t v) :: vs') e t' = Some val ->
      exprD us (vs ++ vs') (substitute' (length vs) w e) t' = Some val.
  Proof.
    intros.
    destruct (@substitute'_lem e (typeof_env vs) w _ eq_refl (typeof_env us) (typeof_env vs') t t').
    { clear - H. rewrite exprD_type_cast in H. forward.
      inv_all; subst. rewrite typeof_env_app in *. auto. }
    { clear - H0. rewrite exprD_type_cast in H0. forward.
      inv_all; subst. rewrite typeof_env_app in *. auto. }
    { unfold exprD in *.
      repeat rewrite split_env_app in *.
      simpl in H0.
      consider (split_env vs);
        consider (split_env vs');
        consider (split_env us); intros.
      repeat match goal with
               | H : _ |- _ =>
                 eapply split_env_typeof_env in H
             end.
      intuition.
      revert H7 H8 H9. subst.
      specialize (H2 h).
      forward; inv_all.
      rewrite H7 in *.
      specialize (@H2 _ _ H0 H).
      forward. rewrite typeof_env_length in *.
      rewrite H2.
      f_equal. rewrite <- H3.
      revert H7 H8 H9. subst.
      auto. }
  Qed.

End substitute.

Section beta.
  Variable ts : types.
  Variable sym : Type.
  Variable RSym_sym : RSym (typD ts) sym.

  Fixpoint beta (e : expr sym) : expr sym :=
    match e with
      | App (Abs t e') e'' =>
        substitute' 0 e'' e'
      | App a x =>
        App (beta a) x
      | e => e
    end.

  Theorem beta_typed
  : forall tus tvs e t,
      typeof_expr tus tvs e = Some t ->
      typeof_expr tus tvs (beta e) = Some t.
  Proof.
    induction e; simpl; intros; auto.
    Opaque beta.
    forward.
    destruct e1; simpl; Cases.rewrite_all; auto.
    simpl in *. forward.
    eapply (substitute'_typed RSym_sym e1 nil); eauto.
    simpl. inv_all; subst.
    simpl in H1. forward.
    Transparent beta.
  Qed.

  Theorem beta_exprD
  : forall us vs e t val,
           exprD us vs e t = Some val ->
           exprD us vs (beta e) t = Some val.
  Proof.
    induction e; simpl; intros; auto.
    Opaque beta.
    destruct e1; simpl; eauto.
    { red_exprD. forward.
      inv_all; subst.
      specialize (IHe1 _ _ H1).
      erewrite beta_typed.
      2: simpl; Cases.rewrite_all; reflexivity.
      simpl. Cases.rewrite_all.
      rewrite typ_cast_typ_refl in *. auto. }
    { red_exprD. forward; inv_all; subst.
      eapply substitute'_exprD with (vs := nil); intros.
      { simpl. eassumption. }
      { simpl.
        red_exprD.
        inversion x0; subst. revert H.
        uip_all'. intros; subst.
        generalize (x1 t5). clear.
        destruct (exprD us (existT (typD ts nil) t2 t5 :: vs) e1 x); auto.
        intros; exfalso; auto. } }
  Qed.

End beta.