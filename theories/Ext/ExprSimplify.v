Require Import List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.Consider.
Require Import MirrorCore.ExprCore.
Require Import MirrorCore.ExprT.
Require Import MirrorCore.ExprSubst.

Set Implicit Arguments.
Set Strict Implicit.

Section reduce.
  Variable ts : types.
  Variable fs : functions ts.
  
  Fixpoint simplifyHd (e : expr ts) : expr ts :=
    match e with
      | App e nil => simplifyHd e
      | App e args =>
        match simplifyHd e with
          | App e args' => App e (args' ++ args)
          | e => App e args
        end
      | _ => e
    end.

  Lemma type_of_apply_app : forall a x b r,
    type_of_apply x (a ++ b) = Some r <->
    exists c, type_of_apply x a = Some c /\
              type_of_apply c b = Some r.
  Proof.
    induction a; simpl.
    { intuition; eauto. destruct H. destruct H.
      inversion H; clear H; subst; auto. }
    { destruct a. intros.
      destruct x. intuition try congruence. destruct H; intuition congruence.
      change typ_eqb with (@rel_dec _ (@eq typ) _).
      consider (x1 ?[ eq ] t); intros; subst. rewrite IHa. intuition.
      intuition try congruence. destruct H0; intuition congruence.
      intuition try congruence. destruct H; intuition congruence.
      intuition try congruence. destruct H; intuition congruence.
      intuition try congruence. destruct H; intuition congruence. }
  Qed.

  Lemma WellTyped_expr_app_flatten : forall tf u g f as1 as2 t,
    WellTyped_expr tf u g (App (@App ts f as1) as2) t <->
    WellTyped_expr tf u g (App f (as1 ++ as2)) t.
  Proof.
    intuition; 
    repeat match goal with
             | [ H : WellTyped_expr _ _ _ (App _ _) _ |- _ ] =>
               apply WellTyped_expr_App in H
             | [ H : exists x, _ |- _ ] =>
               destruct H
             | [ H : _ /\ _ |- _ ] => destruct H
           end.
    { apply WellTyped_expr_App. do 2 eexists.
      split; eauto. split.
      eapply Forall2_app; eauto. rewrite map_app.
      eapply type_of_apply_app. eexists; split; eauto. }
    { eapply Forall2_app_inv_l in H0. destruct H0. destruct H0. intuition; subst.
      rewrite map_app in H1.
      rewrite type_of_apply_app in H1. destruct H1. intuition.
      eapply WellTyped_expr_App. do 2 eexists; split; eauto.
      eapply WellTyped_expr_App. do 2 eexists; split; eauto. }
  Qed.

  Theorem simplifyHd_wt : forall tf e u g t,
    WellTyped_expr tf u g e t ->
    WellTyped_expr tf u g (simplifyHd e) t.
  Proof.
    induction e; simpl; intros; auto.
    destruct es; eauto. 
    { eapply IHe. apply WellTyped_expr_App in H0.
      destruct H0. destruct H0. intuition.
      inversion H0; clear H0; subst. simpl in *. inversion H3; clear H3; subst.
      auto. }
    { apply WellTyped_expr_App in H0. do 2 destruct H0. intuition.
      generalize dependent (e0 :: es); intros.
      specialize (IHe _ _ _ H1). clear e0 es.
      consider (simplifyHd e); simpl in *; intros; try solve [ apply WellTyped_expr_App;
      repeat match goal with
               | [ H : match ?x with _ => _ end = _ |- _ ] =>
                 (consider x; intros; try congruence); [ subst ]
               | [ H : typ_eqb _ _ = true |- _ ] => 
                 change typ_eqb with rel_dec in H; rewrite rel_dec_correct in H; subst
               | [ H : _ = _ |- _ ] => rewrite H
               | [ |- exists x, _ ] => do 2 eexists
               | [ |- _ /\ _ ] => split; eauto; simpl
             end ].
      eapply WellTyped_expr_app_flatten. eapply WellTyped_expr_App. eauto. } 
  Qed.

      Theorem exprD_App : forall u g e es t,
        exprD fs u g (@App ts e es) t = 
        match typeof  fs u (typeof_env g) e with
          | None => None
          | Some tf => 
            match exprD fs u g e tf with
              | None => None
              | Some f => 
                (fix recur tf (f : typD _ _ tf) (es : exprs ts) {struct es} :=
                   match es as es return _ with
                     | nil => match typ_eq_odec tf t with
                                | None => None
                                | Some pf => 
                                  Some match pf in _ = t return typD ts nil t with
                                         | eq_refl => f
                                       end
                              end
                     | e :: es =>
                       match tf as tf return typD _ _ tf -> _ with 
                         | tvArr tf tr =>
                           match exprD fs u g e tf with
                             | None => fun _ => None
                             | Some v => fun f => recur tr (f v) es
                           end
                         | _ => fun _ => None
                       end f
                   end) tf f es
            end
        end.
      Proof.
        unfold exprD. intros; consider (split_env g); intros.
        simpl. generalize (split_env_fst_typeof_env g).
        rewrite H. simpl in *. intros; subst.
        consider (typeof fs u (typeof_env g) e); intros; auto.
        consider (exprD' fs u (typeof_env g) e t0); intros; auto.
        clear. revert t1. revert t0. revert h. revert t. 
        induction es; simpl; intros.
        { simpl. destruct (typ_eq_odec t0 t); subst; auto. }
        { destruct t0; auto.
          destruct (exprD' fs u (typeof_env g) a t0_1); auto.
          rewrite IHes. reflexivity. }
      Qed.


  Theorem simplifyHd_exprD : forall e u g t,
    exprD fs u g e t = exprD fs u g (simplifyHd e) t.
  Proof.
    induction e; simpl; intros; auto.
    destruct es; eauto. 
    { rewrite <- IHe.
      rewrite exprD_App.
      consider (typeof fs u (typeof_env g) e); intros.
      consider (typ_eq_odec t0 t); intros; subst.
      destruct (exprD fs u g e t); auto.
      apply typ_eq_odec_None in H1.
      admit.
      admit. }
    { generalize dependent (e0 :: es); intros.
      admit. }
  Qed.

  Fixpoint apply_all (f : expr ts) (es : exprs ts) : expr ts :=
    match es with
      | nil => f
      | e :: es =>
        match f with
          | Abs t b => apply_all (exprSubstVar 0 0 e b) es
          | _ => App f (e :: es)
        end
    end.

  Fixpoint betaHd (e : expr ts) : expr ts :=
    match e with
      | App e es => 
        apply_all (simplifyHd e) es
      | e => e
    end.

End reduce.
