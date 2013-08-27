Require Import List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.EqDep.
Require Import ExtLib.Tactics.Injection.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.ExprCore.
Require Import MirrorCore.Ext.ExprD.
(*Require Import MirrorCore.Ext.ExprT. *)

Set Implicit Arguments.
Set Strict Implicit.

(** This is a temporary thing **)
Require Import FunctionalExtensionality.

Section semantic.

(*
  Theorem typeof_expr_weaken : forall tfs e uenv venv t,
    typeof_expr tfs uenv venv e = Some t ->
    forall ue ve,
    typeof_expr tfs (uenv ++ ue) (venv ++ ve) e = Some t.
  Proof.
    induction e; intros;
      repeat match goal with
               | [ H : Some _ = Some _ |- _ ] =>
                 inversion H ; clear H ; subst
               | [ H : match ?X with _ => _ end = _ |- _ ] =>
                 (consider X; try congruence); [ intros ]
               | [ |- _ ] =>
                 erewrite nth_error_weaken by eassumption
               | [ H : forall x, _ = _ -> _ |- _ ] =>
                 specialize (H _ eq_refl)
             end; auto.
    { simpl in *. erewrite nth_error_weaken by eassumption. reflexivity. }
    { simpl in *. erewrite nth_error_weaken by eassumption. reflexivity. }
    { eapply WellTyped_expr_App in H0. eapply WellTyped_expr_App.
      destruct H0. exists x.
      intuition.
      { clear - H1 H. revert H.
        induction H1; simpl; auto.
        inversion 1; subst. constructor; eauto. eapply H4; eauto. }
      eapply IHe. eapply H2. }
    { eapply WellTyped_expr_Abs in H. eapply WellTyped_expr_Abs.
      destruct H; intuition; subst.
      eexists x. intuition.
      change (t :: venv ++ ve) with ((t :: venv) ++ ve).
      eapply IHe; eauto. }
    { eapply WellTyped_expr_Equal in H. eapply WellTyped_expr_Equal.
      intuition; subst; auto. eapply IHe1; eauto. eapply IHe2; eauto. }
    { eapply WellTyped_expr_Not in H. eapply WellTyped_expr_Not.
      intuition; eauto. eapply IHe; eauto. }
  Qed.
*)

  Variable types : types.

  Variable fs : functions types.
  Variable uenv : env (typD types).

(*
  Lemma typeof_weaken : forall e venv t,
    typeof fs uenv venv e = Some t ->
    forall ue ve,
    typeof fs (uenv ++ ue) (venv ++ ve) e = Some t.
  Proof.
    induction e; intros;
      repeat match goal with
               | [ H : Some _ = Some _ |- _ ] =>
                 inversion H ; clear H ; subst
               | [ H : match ?X with _ => _ end = _ |- _ ] =>
                 (consider X; try congruence); [ intros ]
               | [ |- _ ] =>
                 erewrite nth_error_weaken by eassumption
               | [ H : forall x, _ = _ -> _ |- _ ] =>
                 specialize (H _ eq_refl)
             end; auto.
    { simpl in *. consider (nth_error venv v); try congruence; intros.
      erewrite nth_error_weaken by eassumption. auto. }
    { simpl in *. consider (nth_error uenv v); try congruence; intros.
      erewrite nth_error_weaken by eassumption. auto. }
    { simpl in *. specialize (IHe venv).
      consider (typeof fs uenv venv e); intros.
      { specialize (IHe _ eq_refl ue ve). rewrite IHe.
        clear - H1 H. generalize dependent t0.
        induction H; simpl in *; intros; auto.
        specialize (H venv). consider (typeof fs uenv venv x); intros.
        specialize (H1 _ eq_refl ue ve). rewrite H1 in *.
        destruct (type_of_apply t0 t1); eauto.
        solve [ eapply fold_left_monadic_fail in H2; intuition ].
        solve [ eapply fold_left_monadic_fail in H2; intuition ]. }
      { solve [ eapply fold_left_monadic_fail in H2; intuition ]. } }
    { simpl in *.
      consider (typeof fs uenv (t :: venv) e); intros; try congruence.
      change (t :: venv ++ ve) with ((t :: venv) ++ ve).
      erewrite IHe by eauto. auto. }
  Qed.
*)

  Theorem exprD'_weaken_Some : forall ue ve e t venv x y,
    exprD' fs uenv venv e t = Some x ->
    exprD' fs (uenv ++ ue) (venv ++ ve) e t = Some y ->
    forall h he, x h = y (hlist_app h he).
  Proof.
    induction e; simpl; intros;
      repeat match goal with
               | |- context [ match ?X with _ => _ end ] =>
                 match type of X with
                   | typ =>
                     (destruct X; try congruence); [ ]
                   | _ => match X with
                            | match _ with _ => _ end => fail 1
                            | _ => consider X; intros; subst
                          end
                 end
               | [ _ : context [ match ?X with _ => _ end ] |- _ ] =>
                 match type of X with
                   | typ =>
                     (destruct X; try congruence); [ ]
                   | _ => match X with
                            | match _ with _ => _ end => fail 1
                            | _ => consider X; intros; subst
                          end
                 end
               | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
             end; auto; try congruence; try reflexivity.
      { repeat match goal with
                 | [ H : context [ @refl_equal ?A ?B ] |- _ ] =>
                   generalize dependent (@refl_equal A B)
               end.
        pattern (nth_error venv v) at 1 3.
        destruct (nth_error venv v); try congruence.
        intros. generalize dependent e0.
        generalize (nth_error_weaken ve venv _ (sym_eq e)); intro.
        pattern (nth_error (venv ++ ve) v) at 1 3.
        rewrite H0. intros.
        destruct (typ_cast_typ types (fun x => x) nil t0 t); try congruence.
        inv_all; subst.
        unfold tenv in *.
        rewrite hlist_nth_hlist_app by eauto with typeclass_instances.
        generalize (cast1 venv ve v).
        generalize (cast2 venv ve v).
        repeat match goal with
                 | |- context [ @eq_refl ?A ?B ] =>
                   generalize (@eq_refl A B)
               end.
        remember (hlist_nth h v).
        generalize y. clear.
        generalize e. destruct (nth_error venv v).
        inv_all. subst. uip_all.
        repeat match goal with
                 | |- context [ @eq_refl ?A ?B ] =>
                   generalize (@eq_refl A B)
               end.
        generalize e0. destruct (nth_error (venv ++ ve) v); intros.
        inv_all; subst. uip_all. reflexivity.
        congruence. congruence. }
      { eapply lookupAs_weaken in H. revert H. instantiate (1 := ue).
        rewrite H0. intuition; inv_all; auto. }
      { eapply typeof_weaken with (ue := ue) (ve := ve) in H0.
        rewrite H0 in *. inv_all; subst.
        specialize (IHe _ _ _ _ H4 H2).
        clear - H H3 H5 IHe. generalize dependent t. generalize dependent t0.
        induction H; intros.
        { match goal with
            | H : match ?X with _ => _ end _ = _ |- _ =>
              destruct X; try congruence
          end.
          inv_all; subst. f_equal. auto. }
        { destruct t0; try congruence.
          repeat match goal with
                   | H : match ?X with _ => _ end = _ |- _ =>
                     consider X; intros; try congruence
                 end.
          specialize (H _ _ _ _ H1 H2).
          eapply IHForall; [ | eassumption | eassumption ].
          { intros. simpl. erewrite IHe. f_equal. eauto. } } }
      { change (t0_1 :: venv ++ ve) with ((t0_1 :: venv) ++ ve) in *.
        specialize (IHe _ _ _ _ H0 H1).
        eapply functional_extensionality. intros.
        erewrite IHe. reflexivity. }
      { erewrite (IHe1 _ _ _ _ H H0).
        erewrite (IHe2 _ _ _ _ H3 H1).
        reflexivity. }
      { erewrite (IHe _ _ _ _ H H0).
        reflexivity. }
  Qed.
*)
  Admitted.

  Theorem exprD_weaken : forall venv e t ue ve x,
    exprD fs uenv venv e t = Some x ->
    exprD fs (uenv ++ ue) (venv ++ ve) e t = Some x.
  Proof.
(*
    unfold exprD; intros. rewrite split_env_app.
    destruct (split_env venv). destruct (split_env ve).
    consider (exprD' fs uenv x0 e t);
    consider (exprD' fs (uenv ++ ue) (x0 ++ x1) e t); intros; try congruence.
    { inversion H1; clear H1; subst.
      generalize (exprD'_weaken_Some _ _ _ H0 H h h0); intros.
      f_equal. eauto. }
    { exfalso. inv_all; subst.
      clear - H0 H. generalize dependent t.
      revert x0; revert x1. induction e; simpl; intros;
      repeat match goal with
               | [ _ : context [ match ?X with _ => _ end ] |- _ ] =>
                 match type of X with
                   | typ =>
                     (destruct X; try congruence); [ ]
                   | _ => match X with
                            | match _ with _ => _ end => fail 1
                            | _ => consider X; intros; subst
                          end
                 end
               | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
             end; eauto; try congruence.
      { repeat match goal with
                 | [ H : context [ @refl_equal ?A ?B ] |- _ ] =>
                   generalize dependent (@refl_equal A B)
               end.
        do 2 intro.
        generalize (nth_error_weaken x1 x0 v).
        pattern (nth_error x0 v) at 1 2 4.
        destruct (nth_error x0 v); try congruence.
        intros.
        generalize dependent e.
        pattern (nth_error (x0 ++ x1) v) at 1 3.
        erewrite nth_error_weaken; intros. 2: eauto.
        match goal with
          | _ : match ?X with _ => _ end = _ |- _ =>
            destruct X; try congruence
        end. }
      { erewrite lookupAs_weaken in H by eassumption. congruence. }
      { erewrite typeof_weaken in H0 by eauto.
        inv_all; subst.
        generalize (@exprD'_weaken_Some _ _ _ _ _ _ _ H2 H4).
        clear - H5 H3 H.
        generalize dependent t3.
        induction H; simpl; intros.
        { match goal with
            | _ : match ?X with _ => _ end _ = _ |- _ =>
              destruct X; congruence
          end. }
        { destruct t3; try congruence.
          consider (exprD' fs uenv x0 x t3_1); intros; try congruence.
          consider (exprD' fs (uenv ++ ue) (x0 ++ x1) x t3_1); intros; try congruence.
          { specialize (@IHForall _ _ H5 _ H3). clear H3 H5.
            generalize (@exprD'_weaken_Some _ _ _ _ _ _ _ H2 H4); intros.
            clear - H1 H3 IHForall. simpl in *.
            eapply IHForall; intros; clear IHForall.
            specialize (H3 h he). specialize (H1 h he).
            rewrite H1. rewrite H3. reflexivity. }
          { eauto. } } }
      { erewrite typeof_weaken in H0 by eauto.
        inversion H0; clear H0; subst.
        eapply IHe. eassumption. eapply H2. }
      { eapply typeof_weaken with (ue := ue) (ve := x1) in H1. rewrite H0 in H1.
        congruence. }
      { eapply IHe; eauto. simpl; eauto. } }
  Qed.
*)
  Admitted.

End semantic.
