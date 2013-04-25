Require Import List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Tactics.Consider.
Require Import ExprCore.

Section semantic.
  Variable ts : types.

  Theorem split_env_app : forall (l l' : env ts), 
    split_env (l ++ l') =
    let (ts,vs) := split_env l in
    let (ts',vs') := split_env l' in
    existT _ (ts ++ ts') (hlist_app vs vs').
  Proof.
    induction l; simpl; intros.
    { destruct (split_env l'); reflexivity. }
    { destruct a. rewrite IHl.
      destruct (split_env l).
      destruct (split_env l'). reflexivity. }
  Qed.

  Variable fs : functions ts.
  Variable uenv : env ts.

  Theorem lookupAs_weaken : forall (a b : env ts) n t x, 
    lookupAs a n t = Some x ->
    lookupAs (a ++ b) n t = Some x.
  Proof.
    clear. unfold lookupAs. intros.
    consider (nth_error a t); intros; try congruence.
    erewrite nth_error_weaken by eassumption. auto.
  Qed.

  Require Import ExtLib.Tactics.EqDep.
  Theorem uip_refl : forall (t : option typ) e, e = eq_refl t. 
  Proof.
    intros. uip_all. reflexivity.
  Qed.

  Theorem typeof_weaken : forall e venv t,
    typeof (ts := ts) fs uenv venv e = Some t ->
    forall ue ve,
    typeof fs (uenv ++ ue) (venv ++ ve) e = Some t.
  Proof.    
    induction e; simpl; intros;
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
    { erewrite IHe by eauto. clear - H1 H.
      generalize dependent t0.
      induction H; simpl; intros; auto.
      consider (typeof fs uenv venv x); intros; try congruence.
      erewrite H by eauto. destruct t0; try congruence.
      destruct (typ_eqb t0_1 t1); auto. }
    { change (t :: venv ++ ve) with ((t :: venv) ++ ve).
      erewrite IHe by eauto. reflexivity. }
  Qed.
 
  Theorem exprD_weaken_Some : forall ue ve e t venv x y, 
    exprD' fs uenv venv e t = Some x ->
    exprD' fs (uenv ++ ue) (venv ++ ve) e t = Some y ->
    forall h he, equiv ts t (x h) (y (hlist_app h he)).
  Proof.
  Admitted.
    
  Theorem exprD_weaken : forall venv e t ue ve x, 
    exprD fs uenv venv e t = Some x ->
    exists y, exprD fs (uenv ++ ue) (venv ++ ve) e t = Some y /\
      equiv ts t x y.
  Proof.
    unfold exprD; intros. rewrite split_env_app.
    destruct (split_env venv). destruct (split_env ve).
    consider (exprD' fs uenv x0 e t); 
    consider (exprD' fs (uenv ++ ue) (x0 ++ x1) e t); intros; try congruence.
    { inversion H1; clear H1; subst.
      revert h0. revert h.
      generalize dependent x0; generalize dependent x1; generalize dependent t.
      clear ve venv. induction e; simpl; intros;
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
             end; auto; try congruence.
      { eexists; split; eauto. reflexivity. }
      { repeat match goal with
                 | [ H : context [ @refl_equal ?A ?B ] |- _ ] =>
                   generalize dependent (@refl_equal A B)
               end.
        pattern (nth_error x0 v) at 2 3.
        destruct (nth_error x0 v); try congruence.
        intros. generalize dependent e.
        generalize (nth_error_weaken x1 x0 _ e0); intro.
        pattern (nth_error (x0 ++ x1) v) at 2 3.
        rewrite H. intros.
        consider (typ_eq_odec t2 t); intros; try congruence.
        inversion H1; clear H1; inversion H2; clear H2; subst.
        eexists; split; eauto.
        uip_all. clear.
        
        rewrite hlist_nth_hlist_app by eauto with typeclass_instances.
        generalize (cast1 x0 x1 v).
        generalize (cast2 x0 x1 v).
        uip_all.
        repeat match goal with
                 | |- context [ @eq_refl ?A ?B ] =>
                   generalize (@eq_refl A B)
               end.
        simpl in *.
        match goal with
          | |- forall x, equiv _ _ (_ ?X) (_ (match _ with
                                                | Some i => fun x => _ ?Z
                                                | None => _
                                              end _)) =>
          change X with Z; generalize Z
        end.
        clear.
        revert e. revert e0. revert e1. generalize e2.
        rewrite <- e2.
        intros.
        rewrite (uip_refl _ e0).
        rewrite (uip_refl _ e4).
        uip_all.
        clear.
        generalize dependent (nth_error (x0 ++ x1) v).
        intros; subst.
        rewrite (uip_refl _ e6).
        reflexivity. }
      { eexists; split; eauto. clear.
        generalize dependent (instantiate_typ (rev ts0) (ftype f0)). reflexivity. }
      { admit. }
      { eexists; split; eauto.
        simpl; intro.
        eapply IHe with (h := Hcons a h) (h0 := h0) in H0; eauto. 
        destruct H0. destruct H0. inversion H0; clear H0; subst. auto. }        
      { eexists; split; eauto.
        unfold lookupAs in *. 
        consider (nth_error uenv v); try congruence; intros.
        erewrite nth_error_weaken in H by eauto.
        consider (typ_eq_odec (projT1 s) t); intros; try congruence.
        subst. inversion H1; inversion H2; clear H1 H2; subst. reflexivity. }
      { eexists; split; eauto.
        destruct (IHe1 _ _ _ _ H _ H0 h h0).
        destruct (IHe2 _ _ _ _ H3 _ H1 h h0).
        destruct H2; destruct H4.
        inversion H2; inversion H4; clear H2 H4; subst.
        simpl. intuition.
        { etransitivity. symmetry; eauto. etransitivity; eauto. }
        { etransitivity. eauto. etransitivity; eauto. symmetry; eauto. } }
      { eexists; split; eauto.
        destruct (IHe _ _ _ _ H _ H0 h h0).
        destruct H1. inversion H1; clear H1; subst. simpl.
        intuition; eapply H1; eapply H2; auto. } }
    { exfalso. inversion H1; clear H1; subst.
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
        pattern (nth_error x0 v) at 2 3. destruct (nth_error x0 v); try congruence.
        intros. 
        generalize dependent e.
        pattern (nth_error (x0 ++ x1) v) at 2 3.
        erewrite nth_error_weaken by eassumption; intros.
        destruct (typ_eq_odec t1 t); try congruence. }
      { erewrite typeof_weaken in H0 by eauto.
        inversion H0; clear H0; subst.
        generalize (exprD_weaken_Some _ _ _ _ _ _ _ H2 H4).
        clear - H5 H3 H.
        generalize dependent t3.
        induction H; simpl; intros.
        { destruct (typ_eq_odec t3 t); subst; congruence. }
        { destruct t3; try congruence.
          consider (exprD' fs uenv x0 x t3_1); intros; try congruence.
          consider (exprD' fs (uenv ++ ue) (x0 ++ x1) x t3_1); intros; try congruence.
          { specialize (@IHForall _ _ H5 _ H3). clear H3 H5.
            generalize (exprD_weaken_Some _ _ _ _ _ _ _ H2 H4); intros.
            clear - H1 H3 IHForall. simpl in *.
            eapply IHForall; intros; clear IHForall.
            specialize (H3 h he). specialize (H1 h he).
            etransitivity. eapply H1. clear H1. admit.
            (* TODO: I have to know that the function respects the equivalence *) }
          { eauto. } } }            
      { erewrite typeof_weaken in H0 by eauto.
        inversion H0; clear H0; subst.
        eapply IHe. eassumption. eapply H2. }
      { eapply typeof_weaken with (ue := ue) (ve := x1) in H1. rewrite H0 in H1.
        congruence. }
      { eapply IHe; eauto. simpl; eauto. }
      { unfold lookupAs in *.
        consider (nth_error uenv v); try congruence; intros.
        erewrite nth_error_weaken in H by eassumption.
        consider (typ_eq_odec (projT1 s) t); congruence. } }
  Qed.

End semantic.