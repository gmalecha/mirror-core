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

  Fixpoint equiv_env (es1 es2 : env ts) : Prop :=
    match es1 , es2 with
      | nil , nil => True
      | existT t1 v1 :: es1 , existT t2 v2 :: es2 =>
        (exists pf : t2 = t1,
          equiv ts t1 v1 match pf in _ = t return typD ts nil t with
                           | eq_refl => v2 
                         end)
        /\ equiv_env es1 es2
      | _ , _ => False
    end.

  Fixpoint equiv_hlist ls (h1 : hlist (typD ts (@nil Type)) ls) : hlist (typD ts (@nil Type)) ls -> Prop :=
    match h1 in hlist _ ls return hlist (typD ts (@nil Type)) ls -> Prop with
      | Hnil => fun _ => True
      | Hcons t _ h1 hs1 => fun h2 => 
        equiv ts t h1 (hlist_hd h2) /\ equiv_hlist _ hs1 (hlist_tl h2)
    end.
  Require Import RelationClasses.
  Global Instance Reflexive_equiv_hlist ls : Reflexive (@equiv_hlist ls).
  Proof.
    red. induction x; simpl; auto.
    split; auto. reflexivity.
  Qed.
  Global Instance Symmetric_equiv_hlist ls : Symmetric (@equiv_hlist ls).
  Proof.
    red. induction x; intros; rewrite (hlist_eta y) in *; simpl; auto.
    simpl in H. destruct H. split; auto. symmetry. auto.
  Qed.
  Global Instance Transitive_equiv_hlist ls : Transitive (@equiv_hlist ls).
  Proof.
    red. induction x; intros; rewrite (hlist_eta y) in *; rewrite (hlist_eta z) in *; simpl; auto.
    simpl in *. destruct H; destruct H0. split; try etransitivity; eauto.
  Qed.

  Require Import Morphisms.

  

  Theorem exprD'_weaken_Some : forall ue ve e t venv x y, 
    exprD' fs uenv venv e t = Some x ->
    exprD' fs (uenv ++ ue) (venv ++ ve) e t = Some y ->
    forall h he, equiv ts t (x h) (y (hlist_app h he)).
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
        pattern (nth_error venv v) at 2 3.
        destruct (nth_error venv v); try congruence.
        intros. generalize dependent e0.
        generalize (nth_error_weaken ve venv _ e); intro.
        pattern (nth_error (venv ++ ve) v) at 2 3.
        rewrite H0. intros.
        consider (typ_eq_odec t0 t); intros; try congruence.
        inversion H1; inversion H2; clear H1 H2; subst.
        uip_all. clear.
        
        rewrite hlist_nth_hlist_app by eauto with typeclass_instances.
        generalize (cast1 venv ve v).
        generalize (cast2 venv ve v).
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
        generalize dependent (nth_error (venv ++ ve) v).
        intros; subst.
        rewrite (uip_refl _ e6).
        reflexivity. }
      { unfold lookupAs in *. 
        consider (nth_error uenv v); try congruence; intros.
        erewrite nth_error_weaken in H0 by eauto.
        consider (typ_eq_odec (projT1 s) t); intros; try congruence.
        subst. inversion H1; inversion H2; clear H1 H2; subst. reflexivity. }
      { eapply typeof_weaken with (ve := ve) (ue := ue) in H0.
        rewrite H1 in *.
        inversion H0; clear H0; subst.
        specialize (IHe _ _ _ _ H4 H2); clear H2 H4.
        clear - IHe H5 H3 H.
        revert H5 H3 IHe. generalize dependent t2. generalize dependent t.
        induction H; simpl; intros.
        { destruct (typ_eq_odec t2 t); intros; subst; try congruence.
          inversion H5; inversion H3; clear H5 H3; subst.
          eauto. }
        { destruct t2; try congruence.
          consider (exprD' fs uenv venv x t2_1); intros; try congruence.
          consider (exprD' fs (uenv ++ ue) (venv ++ ve) x t2_1); intros; try congruence.
          specialize (H _ _ _ _ H1 H2 h he); clear H1 H2.
          specialize (IHForall _ _ _ _ _ _ H5 H3); clear H5 H3 H0.
          eapply IHForall; intros; simpl in *; clear IHForall.
          etransitivity. eapply IHe; clear IHe.
          instantiate (1 := he0). clear - H. admit. } }
      { simpl; intro. specialize (@IHe _ _ _ _ H H0 (Hcons a h) he); auto. }
      { specialize (IHe1 _ _ _ _ H H0 h he).
        specialize (IHe2 _ _ _ _ H3 H1 h he).
        simpl. intuition.
        { etransitivity. symmetry; eauto. etransitivity; eauto. }
        { etransitivity. eauto. etransitivity; eauto. symmetry; eauto. } }
      { specialize (IHe _ _ _ _ H H0 h he).
        simpl in *. intuition. }
  Qed.
    
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
      generalize (exprD'_weaken_Some _ _ _ _ _ _ _ H0 H h h0); intros.
      eexists; split; eauto. }
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
      { unfold lookupAs in *.
        consider (nth_error uenv v); try congruence; intros.
        erewrite nth_error_weaken in H by eassumption.
        consider (typ_eq_odec (projT1 s) t); congruence. }
      { erewrite typeof_weaken in H0 by eauto.
        inversion H0; clear H0; subst.
        generalize (exprD'_weaken_Some _ _ _ _ _ _ _ H2 H4).
        clear - H5 H3 H.
        generalize dependent t3.
        induction H; simpl; intros.
        { destruct (typ_eq_odec t3 t); subst; congruence. }
        { destruct t3; try congruence.
          consider (exprD' fs uenv x0 x t3_1); intros; try congruence.
          consider (exprD' fs (uenv ++ ue) (x0 ++ x1) x t3_1); intros; try congruence.
          { specialize (@IHForall _ _ H5 _ H3). clear H3 H5.
            generalize (exprD'_weaken_Some _ _ _ _ _ _ _ H2 H4); intros.
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
      { eapply IHe; eauto. simpl; eauto. } }
  Qed.

End semantic.
