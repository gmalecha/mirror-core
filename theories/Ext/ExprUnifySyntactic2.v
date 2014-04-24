Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.Injection.
Require Import ExtLib.Tactics.EqDep.
Require Import ExtLib.Tactics.Cases.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.SubstI2.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.ExprCore.
Require Import MirrorCore.Ext.ExprT.
Require Import MirrorCore.Ext.ExprD.
Require Import MirrorCore.Ext.ExprLift.

(** TODO **)
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Set Strict Implicit.

Section typed.
  Variable subst : Type.
  Variable types : Types.types.
  Variable func : Type.
  Variable RSym_func : RSym (typD types) func.
  Variable RSymOk_func : RSymOk RSym_func.
  Variable Subst_subst : Subst subst (expr func).
  Variable SubstUpdate_subst : SubstUpdate subst (expr func).
  Variable SubstOk_subst : SubstOk (Expr_expr RSym_func) Subst_subst.
  Variable SubstUpdateOk_subst : @SubstUpdateOk _ _ _ _ (Expr_expr RSym_func) _ SubstUpdate_subst _.

  Section nested.

  (** n is the number of binders that we have gone under **)
  Variable exprUnify : forall (us vs : tenv typ) (under : nat) (s : subst)
                              (l r : expr func), typ -> option subst.

  Fixpoint exprUnify' (us vs : tenv typ) (n : nat) (s : subst)
           (e1 e2 : expr func) (t : typ) {struct e1}
  : option subst.
  refine (
    match e1 , e2 with
      | UVar u1 , UVar u2 =>
        if EqNat.beq_nat u1 u2 then Some s
        else
          match lookup u1 s , lookup u2 s with
            | None , None =>
              match set u1 (UVar u2) s with
                | None =>
                  set u2 (UVar u1) s
                | Some s => Some s
              end
            | Some e1' , None =>
              set u2 e1' s
            | None , Some e2' =>
              set u1 e2' s
            | Some e1' , Some e2' =>
              exprUnify us vs n s (lift 0 n e1') (lift 0 n e2') t
          end
      | UVar u1 , _ =>
        match lookup u1 s with
          | None =>
            match lower 0 n e2 with
              | None => None
              | Some e2 => set u1 e2 s
            end
          | Some e1' => exprUnify us vs n s (lift 0 n e1') e2 t
        end
      | _ , UVar u2 =>
        match lookup u2 s with
          | None =>
            match lower 0 n e1 with
              | None => None
              | Some e1 => set u2 e1 s
            end
          | Some e2' => exprUnify us vs n s e1 (lift 0 n e2') t
        end
      | Var v1 , Var v2 =>
        if EqNat.beq_nat v1 v2 then Some s else None
      | Inj f1 , Inj f2 =>
        match sym_eqb f1 f2 with
          | Some true => Some s
          | _ => None
        end
      | App e1 e1' , App e2 e2' =>
        match typeof_expr us vs e1 , typeof_expr us vs e2 with
          | Some (tyArr l r) , Some (tyArr l' r') =>
            if l ?[ eq ] l' && r ?[ eq ] r' && t ?[ eq ] r then
              match exprUnify' us vs n s e1 e2 (tyArr l t) with
                | None => None
                | Some s' =>
                  exprUnify' us vs n s' e1' e2' l
              end
            else
              None
          | _ , _ => None
        end
      | Abs t1 e1 , Abs t2 e2 =>
        (* t1 = t2 since both terms have the same type *)
        match t with
          | tyArr _ t =>
            exprUnify' us (t1 :: vs) (S n) s e1 e2 t
          | _ => None
        end
      | _ , _ => None
    end)%bool.
  Defined.
  End nested.

  Section exprUnify.

    Fixpoint exprUnify (fuel : nat) (us vs : tenv typ) (under : nat) (s : subst)
             (e1 e2 : expr func) (t : typ) : option subst :=
      match fuel with
        | 0 => None
        | S fuel =>
          exprUnify' (exprUnify fuel) us vs under s e1 e2 t
      end.
  End exprUnify.

(* TODO: You can only avoid functional extensionality if you use exprD'
  Definition unify_sound_ind'
    (unify : forall (us vs : tenv typ) (under : nat) (s : subst) (l r : expr func)
                    (t : typ), option subst) : Prop :=
    forall tu tv e1 e2 s s' t tv',
      WellFormed_subst s ->
      WellTyped_expr tu (tv' ++ tv) e1 t ->
      WellTyped_expr tu (tv' ++ tv) e2 t ->
      WellTyped_subst (SubstOk := SubstOk_subst) tu tv s ->
      unify tu (tv' ++ tv) (length tv') s e1 e2 t = Some s' ->
         WellFormed_subst s'
      /\ WellTyped_subst (SubstOk := SubstOk_subst) tu tv s'
      /\ (forall u v,
            WellTyped_env tu u ->
            WellTyped_env tv v ->
            Forall (fun x => x) (substD (SubstOk := SubstOk_subst) u v s') ->
               Forall (fun x => x) (substD (SubstOk := SubstOk_subst) u v s)
            /\ forall v',
                 WellTyped_env tv' v' ->
                 exprD u (v' ++ v) e1 t = exprD u (v' ++ v) e2 t).
*)

  Definition unify_sound_ind
    (unify : forall (us vs : tenv typ) (under : nat) (s : subst) (l r : expr func)
                    (t : typ), option subst) : Prop :=
    forall tu tv e1 e2 s s' t tv',
      WellFormed_subst s ->
      WellTyped_expr tu (tv' ++ tv) e1 t ->
      WellTyped_expr tu (tv' ++ tv) e2 t ->
      WellTyped_subst (SubstOk := SubstOk_subst) tu tv s ->
      unify tu (tv' ++ tv) (length tv') s e1 e2 t = Some s' ->
         WellFormed_subst s'
      /\ WellTyped_subst (SubstOk := SubstOk_subst) tu tv s'
      /\ (forall u v,
            WellTyped_env tu u ->
            WellTyped_env tv v ->
            substD (SubstOk := SubstOk_subst) u v s' ->
               substD (SubstOk := SubstOk_subst) u v s
            /\ forall v',
                 WellTyped_env tv' v' ->
                 exprD u (v' ++ v) e1 t = exprD u (v' ++ v) e2 t).

  Definition unify_sound := unify_sound_ind.

  Ltac forward_reason :=
    repeat match goal with
             | H : exists x, _ |- _ =>
               destruct H
             | H : _ /\ _ |- _ => destruct H
             | H' : ?X , H : ?X -> ?Y |- _ =>
               match type of X with
                 | Prop => specialize (H H')
               end
             | H : ?X -> ?Y |- _ =>
               match type of X with
                 | Prop =>
                   let H' := fresh in
                   assert (H' : X) by eauto ;
                   specialize (H H') ;
                   clear H'
               end
           end.

  Lemma handle_set : forall
    (unify : tenv typ -> tenv typ -> nat -> subst ->
             expr func -> expr func -> typ -> option subst),
    unify_sound_ind unify ->
    forall (tu : tenv typ) (tv : list typ) (u : uvar)
           (s s' : subst) (t : typ) (tv' : list typ)
    (wf : WellFormed_subst s),
      WellTyped_expr tu (tv' ++ tv) (UVar u) t ->
      WellTyped_subst tu tv s ->
      forall e e' : expr func,
        WellTyped_expr tu (tv' ++ tv) e t ->
        lower 0 (length tv') e = Some e' ->
        lookup u s = None ->
        set u e' s = @Some subst s' ->
        WellFormed_subst s' /\
        WellTyped_subst tu tv s' /\
        (forall u0 v : @env typ (typD types),
           @WellTyped_env types tu u0 ->
           @WellTyped_env types tv v ->
           substD u0 v s' ->
           substD u0 v s /\
           (forall v' : @env typ (typD types),
              @WellTyped_env types tv' v' ->
              exprD u0 (v' ++ v) (UVar u) t =
              exprD u0 (v' ++ v) e t)).
  Proof.
    intros.
    split.
    { eapply WellFormed_set; eauto with typeclass_instances. }
    split.
    { eapply WellTyped_set; eauto.
      simpl. red. generalize (typeof_expr_lower _ tu e nil tv' tv).
      simpl. intro. rewrite <- H6; eauto. }
    { intros.
      generalize H3. intro.
      consider (nth_error u0 u).
      { intros.
        destruct (@substD_set _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ wf H8 H4 H5).
        split; auto. intros.
        rewrite WellTyped_expr_UVar in H0.
        eapply WellTyped_env_typeof_env in H6. subst.
        unfold typeof_env in H0. rewrite nth_error_map in H0.
        autorewrite with exprD_rw. unfold lookupAs.
        forward. subst. simpl in *. inv_all; subst.
        rewrite typ_cast_typ_refl. simpl in *.
        simpl in *.
        change 0 with (length (@nil (sigT (typD types nil)))) in H9.
        cutrewrite (length tv' = length v') in H9.
        eapply exprD_lower in H9.
        symmetry. etransitivity. eapply H9. simpl in *.
        specialize (H12 _ eq_refl). simpl in H12. auto.
        apply WellTyped_env_typeof_env in H13. subst.
        rewrite typeof_env_length. reflexivity. }
      { intro. exfalso.
        red in H0. simpl in H0.
        eapply WellTyped_env_typeof_env in H6.
        subst. rewrite nth_error_typeof_env in *.
        rewrite H10 in *. congruence. } }
  Qed.

  Lemma handle_uvar
  : forall (unify : tenv typ -> tenv typ -> nat -> subst ->
                    expr func -> expr func -> typ -> option subst),
      unify_sound_ind unify ->
      forall (tu : tenv typ) (tv : list typ) (u : uvar)
             (s s' : subst) (t : typ) (tv' : list typ),
        WellFormed_subst s ->
        WellTyped_expr  tu (tv' ++ tv) (UVar u) t ->
        WellTyped_subst tu tv s ->
        forall e : expr func,
          WellTyped_expr tu (tv' ++ tv) e t ->
          match lookup u s with
            | Some e2' =>
              unify tu (tv' ++ tv) (@length typ tv') s e
                    (lift 0 (@length typ tv') e2') t
            | None =>
              match lower 0 (@length typ tv') e with
                | Some e1 => set u e1 s
                | None => @None subst
              end
          end = @Some subst s' ->
          WellFormed_subst s' /\
          WellTyped_subst tu tv s' /\
          (forall u0 v : @env typ (typD types),
             WellTyped_env tu u0 ->
             WellTyped_env tv v ->
             substD u0 v s' ->
             substD u0 v s /\
             (forall v' : @env typ (typD types),
                WellTyped_env tv' v' ->
                exprD u0 (v' ++ v) e t =
                exprD u0 (v' ++ v) (UVar u) t)).
  Proof.
    intros.
    consider (lookup u s); intros.
    { eapply H in H5; eauto using WellTyped_lookup.
      { forward_reason.
        split; auto. split; auto.
        intros.
        specialize (H7 u0 v). forward_reason.
        split; auto. intros.
        specialize (H11 v'). forward_reason.
        rewrite H11.
        autorewrite with exprD_rw.
        unfold lookupAs.
        eapply substD_lookup in H4; eauto.
        forward_reason.
        rewrite H4. destruct x.
        assert (x = t).
        { rewrite WellTyped_expr_UVar in H1.
          eapply WellTyped_env_typeof_env in H8. subst.
          unfold typeof_env in H1.
          rewrite nth_error_map in H1. rewrite H4 in *. inv_all.
          simpl in *. auto. }
        subst. simpl. rewrite typ_cast_typ_refl. simpl in *.
        generalize (exprD_lift _ u0 nil v' v e0 t). simpl.
        cutrewrite (length v' = length tv').
        { intro X. etransitivity. eapply X. auto. }
        { eapply WellTyped_env_typeof_env in H12. subst.
          rewrite typeof_env_length. auto. } }
      { eapply WellTyped_lookup in H4. 2: eauto. 2: eauto.
        unfold WellTyped_expr in *.
        simpl in *. rewrite H1 in *.
        destruct H4. intuition; inv_all; subst.
        generalize (typeof_expr_lift _ tu nil tv' tv e0); simpl.
        intros. red in H7. etransitivity; eauto. } }
    { match goal with
        | _ : match ?X with _ => _ end = _ |- _ =>
          consider X; try congruence; intros
      end.
      eapply handle_set in H5; eauto.
      forward_reason.
      split; auto. split; auto.
      intros. specialize (H8 u0 v); forward_reason.
      split; auto. intros.
      specialize (H12 v'); forward_reason.
      symmetry; auto. }
  Qed.

  Lemma handle_uvar2
  : forall
      (unify : tenv typ ->
             tenv typ -> nat -> subst -> expr func -> expr func -> typ -> option subst),
      unify_sound_ind unify ->
   forall (tu : tenv typ) (tv : list typ) (u : uvar)
     (s s' : subst) (t : typ) (tv' : list typ)
     (wf : WellFormed_subst s),
     WellTyped_expr tu (tv' ++ tv) (UVar u) t ->
     WellTyped_subst tu tv s ->
     forall e : expr func,
       WellTyped_expr tu (tv' ++ tv) e t ->
       match lookup u s with
         | Some e2' =>
           unify tu (tv' ++ tv) (@length typ tv') s
                 (lift 0 (@length typ tv') e2') e t
         | None =>
           match lower 0 (@length typ tv') e with
             | Some e1 => set u e1 s
             | None => @None subst
           end
       end = @Some subst s' ->
       WellFormed_subst s' /\
       WellTyped_subst tu tv s' /\
       (forall u0 v : @env typ (typD types),
          WellTyped_env tu u0 ->
          WellTyped_env tv v ->
          substD u0 v s' ->
          substD u0 v s /\
          (forall v' : @env typ (typD types),
             WellTyped_env tv' v' ->
             exprD u0 (v' ++ v) (UVar u) t =
             exprD u0 (v' ++ v) e t)).
  Proof.
    intros.
    consider (lookup u s); intros.
    { eapply H in H4; eauto using WellTyped_lookup.
      { forward_reason.
        split; auto. split; auto.
        intros.
        specialize (H6 u0 v). forward_reason.
        split; auto. intros. specialize (H10 v'); forward_reason.
        autorewrite with exprD_rw.
        unfold lookupAs.
        eapply substD_lookup in H3; eauto.
        forward_reason.
        destruct x. simpl in *.
        assert (x = t).
        { rewrite WellTyped_expr_UVar in H0.
          eapply WellTyped_env_typeof_env in H7. subst.
          unfold typeof_env in H0.
          rewrite nth_error_map in H0. rewrite H3 in *. inv_all.
          simpl in *. auto. }
        rewrite H3.
        subst. rewrite typ_cast_typ_refl. symmetry.  etransitivity. symmetry.
        eassumption.
        generalize (exprD_lift _ u0 nil v' v e0 t). simpl.
        cutrewrite (length v' = length tv').
        { intro X. etransitivity. eapply X. auto. }
        { eapply WellTyped_env_typeof_env in H11. subst.
          rewrite typeof_env_length. auto. } }
      { eapply WellTyped_lookup in H3. 2: eauto. 2: eauto.
        unfold WellTyped_expr in *.
        simpl in *. rewrite H0 in *.
        destruct H3; intuition; inv_all; subst.
        generalize (typeof_expr_lift _ tu nil tv' tv e0); simpl.
        intros. etransitivity; eassumption. } }
    { match goal with
        | _ : match ?X with _ => _ end = _ |- _ =>
          consider X; try congruence; intros
      end.
      eapply handle_set in H5; eauto. }
  Qed.

  Lemma WellTyped_from_subst : forall tu tv tv' s e t u,
    WellFormed_subst s ->
    WellTyped_subst tu tv s ->
    WellTyped_expr tu (tv' ++ tv) (UVar u) t ->
    lookup u s = Some e ->
    WellTyped_expr tu (tv' ++ tv) (lift 0 (length tv') e) t.
  Proof.
    intros.
    rewrite WellTyped_expr_UVar in H1.
    eapply WellTyped_lookup in H0; eauto.
    destruct H0 as [ ? [ ? ? ] ].
    simpl in H3.
    etransitivity.
    eapply (typeof_expr_lift _ tu nil tv' tv e).
    rewrite H1 in *. inv_all; subst.
    exact H3.
  Qed.

  Lemma exprD_from_subst : forall us vs vs' s e u t,
    WellFormed_subst s ->
    substD us vs s ->
    lookup u s = Some e ->
    nth_error (typeof_env us) u = Some t ->
    exprD us (vs' ++ vs) (UVar u) t =
    exprD us (vs' ++ vs) (lift 0 (length vs') e) t.
  Proof.
    intros.
    rewrite exprD_UVar.
    unfold lookupAs.
    generalize H1.
    eapply substD_lookup in H1; eauto.
    destruct H1. intuition.
    rewrite nth_error_typeof_env in *.
    rewrite H4 in *. destruct x; inv_all; subst. simpl in *.
    rewrite typ_cast_typ_refl.
    symmetry. etransitivity. eapply (exprD_lift _ us nil vs' vs).
    eapply H5.
  Qed.

  Lemma nth_error_from_WellTyped_UVar : forall tu tv u us t,
    WellTyped_expr tu tv (UVar u) t ->
    WellTyped_env (types := types) tu us ->
    nth_error (typeof_env us) u = Some t.
  Proof.
    intros.
    rewrite WellTyped_expr_UVar in *.
    rewrite WellTyped_env_typeof_env in *. subst. auto.
  Qed.

  Lemma exprUnify'_sound : forall unify,
                             unify_sound_ind unify ->
                             unify_sound_ind (exprUnify' unify).
  Proof.
    Opaque rel_dec.
    red. induction e1; simpl; intros.
    { destruct e2; try congruence; eauto using handle_uvar.
      { consider (EqNat.beq_nat v v0); intros; try congruence.
        inv_all; subst. intuition. } }
    { destruct e2; try congruence; eauto using handle_uvar.
       consider (sym_eqb f f0); try congruence; intros.
       destruct b; try congruence. inv_all; subst.
       generalize (@sym_eqbOk _ _ _ _ RSymOk_func f f0).
       rewrite H4. intros; subst. intuition. }
    { destruct e2; try congruence; eauto using handle_uvar.
      { repeat match goal with
                 | H : match ?X with _ => _ end = _ |- _ =>
                   (consider X; try congruence); [ intros ]
                 | H : not (match ?X with _ => _ end = _) |- _ =>
                   (consider X; try congruence); [ intros ]
                 | H : _ /\ _ |- _ => destruct H
                 | H : not (Some _ = None) |- _ => clear H
               end.
        subst.
        eapply WellTyped_expr_App in H1.
        eapply WellTyped_expr_App in H2.
        specialize (IHe1_1 e2_1 s s0 (tyArr t4 t5) tv').
        specialize (IHe1_2 e2_2 s0 s' t4 tv').
        unfold WellTyped_expr in *.
        forward_reason.
        rewrite H7 in *. inv_all; subst.
        simpl in H6. forward; inv_all; subst.
        unfold type_of_apply in H11.
        forward; inv_all; subst. clear H6.
        rewrite H5 in H2.
        inv_all. subst. 
        forward_reason.
        split; eauto. split; eauto.
        intros.
        specialize (H14 u v H15 H16).
        specialize (H11 u v H15 H16).
        forward_reason.
        split; auto. intros.
        specialize (H18 v').
        specialize (H19 v').
        forward_reason.
        autorewrite with exprD_rw.
        assert (tu = typeof_env u) by (eapply WellTyped_env_typeof_env; assumption).
        assert (tv = typeof_env v) by (eapply WellTyped_env_typeof_env; assumption).
        assert (tv' = typeof_env v') by (eapply WellTyped_env_typeof_env; assumption).
        subst. repeat rewrite typeof_env_app in *.
        Cases.rewrite_all_goal. reflexivity. } }
    { destruct e2; try congruence; eauto using handle_uvar.
      { forward. subst.
        specialize (IHe1 e2 s s' t3 (t :: tv')). simpl in *.
        eapply WellTyped_expr_Abs in H2. eapply WellTyped_expr_Abs in H4.
        forward_reason.
        inversion H2; clear H2; inversion H1; clear H1; subst. subst.
        forward_reason.
        split; auto. split; auto. intros.
        specialize (H7 u v). forward_reason.
        split; auto. intros.
        assert (tu = typeof_env u) by (eapply WellTyped_env_typeof_env; assumption).
        assert (tv = typeof_env v) by (eapply WellTyped_env_typeof_env; assumption).
        assert (tv' = typeof_env v') by (eapply WellTyped_env_typeof_env; assumption); subst.
        generalize (@typeof_expr_eq_exprD_False _ _ _ u (v' ++ v) t1 e1 x).
        generalize (@typeof_expr_eq_exprD_False _ _ _ u (v' ++ v) t1 e2 x).
        unfold typecheck_expr, WellTyped_expr in *.
        erewrite typeof_env_app.
        intros; forward_reason.
        unfold exprD.
        intros. unfold exprD in *. simpl in *. remember (split_env (v' ++ v)).
        destruct s0.
        simpl in *.
        consider (split_env u); intros.
        repeat rewrite exprD'_Abs.
        rewrite typ_cast_typ_refl.
        generalize typeof_expr_exprD'. unfold WellTyped_expr.
        intro XXX. rewrite XXX in H4. rewrite XXX in H6.
        assert (typeof_env v' ++ typeof_env v = x0).
        { rewrite <- typeof_env_app.
          generalize (@split_env_projT1 _ _ (v' ++ v)).
          rewrite <- Heqs0. simpl. intro. symmetry. exact H16. }
        assert (typeof_env u = x1).
        { generalize (@split_env_projT1 _ _ u).
          rewrite H11. simpl. intro. symmetry. exact H17. }
        subst. forward_reason.
        Cases.rewrite_all_goal.
        f_equal.
        eapply functional_extensionality; intros.
        specialize (H14 x2). specialize (H15 x2).
        specialize (H13 (existT _ t1 x2  :: v')). simpl in *.
        rewrite <- Heqs0 in *. simpl in *.
        assert (WellTyped_env (t1 :: typeof_env v') (existT (typD types nil) t1 x2 :: v')).
        { constructor; auto. }
        forward_reason.
        forward. inv_all; subst. auto. } }
    { destruct e2; eauto using handle_uvar2.
      { consider (EqNat.beq_nat u u0); intros; inv_all; subst.
        { intuition. }
        { consider (lookup u s); consider (lookup u0 s); intros.
          { eapply H in H7; eauto using WellTyped_from_subst.
            forward_reason.
            split; auto. split; auto.
            intros. specialize (H9 u1 v).
            forward_reason.
            split; auto. intros.
            specialize (H13 v'). forward_reason.
            eapply nth_error_from_WellTyped_UVar in H1; eauto.
            eapply nth_error_from_WellTyped_UVar in H2; eauto.
            rewrite WellTyped_env_typeof_env in *. subst.
            rewrite typeof_env_length in *.
            erewrite exprD_from_subst. 4: eauto. 2: eauto. 2: eauto. 2: eauto.
            erewrite exprD_from_subst. 4: eauto. 2: eauto. 2: eauto. 2: eauto.
            eauto. }
          { generalize H6. eapply WellTyped_lookup in H6; eauto.
            forward_reason.
            generalize H7.
            eapply WellTyped_set in H7; eauto.
            { intros. split.
              { eapply WellFormed_set; eauto. }
              split; auto.
              intros.
              assert (exists v, nth_error u1 u0 = Some (existT _ t v)).
              { clear - H2 H11.
                red in H2. simpl in H2.
                eapply WellTyped_env_typeof_env in H11. subst.
                rewrite nth_error_typeof_env in H2. forward.
                inv_all. subst. destruct s. simpl. eauto. }
              destruct H14.
              eapply substD_set in H9; eauto.
              forward_reason. split; auto. intros.
              erewrite exprD_from_subst; eauto using nth_error_from_WellTyped_UVar.
              rewrite exprD_UVar.
              rewrite WellTyped_expr_UVar in *.
              unfold lookupAs.
              eapply WellTyped_env_typeof_env in H11. subst.
              rewrite nth_error_typeof_env in H2.
              destruct (nth_error u1 u0); try congruence.
              destruct s0; simpl in *; inv_all. clear H2. subst.
              rewrite typ_cast_typ_refl.
              etransitivity.
              eapply (exprD_lift _ u1 nil v' v e x1). auto.
              specialize (H15 _ eq_refl). apply H15. }
            { red in H1; simpl in *.
              rewrite H1 in H6; inv_all; subst; auto. } }
          { generalize H5. eapply WellTyped_lookup in H5; eauto.
            destruct H5.
            assert (x = t); subst.
            { simpl in *. rewrite H2 in *.
              intuition; inv_all; auto. }
            { split.
              { eapply WellFormed_set; eauto. }
              forward_reason.
              split.
              { eapply WellTyped_set in H7; eauto. }
              intros.
              assert (exists v, nth_error u1 u = Some (existT _ t v)).
              { clear - H1 H10.
                red in H1. simpl in H1.
                eapply WellTyped_env_typeof_env in H10. subst.
                rewrite nth_error_typeof_env in H1. forward.
                inv_all. subst. destruct s. simpl. eauto. }
              destruct H13.
              eapply substD_set in H7; eauto.
              forward_reason.
              split; auto. intros.
              erewrite exprD_from_subst with (u := u0); eauto using (fun x => @nth_error_from_WellTyped_UVar x tv).
              rewrite exprD_UVar.
              rewrite WellTyped_expr_UVar in *.
              unfold lookupAs.
              eapply WellTyped_env_typeof_env in H10. subst.
              rewrite nth_error_typeof_env in *.
              destruct (nth_error u1 u); try congruence.
              forward. subst. inv_all; subst. simpl in *. subst.
              rewrite typ_cast_typ_refl.
              etransitivity. symmetry; auto.
              symmetry.
              rewrite (exprD_lift _ u1 nil v' v e (projT1 s1)). auto.
              eapply (H14 _ eq_refl). } }
          { consider (set u (UVar u0) s); intros; inv_all; subst.
            { eapply handle_uvar2; eauto.
              rewrite H6. rewrite lower_lower'. simpl. auto. }
            { eapply handle_uvar; eauto.
              rewrite H5. rewrite lower_lower'. simpl. auto. } } } } }
  Qed.

  Theorem exprUnify_sound : forall fuel, unify_sound (exprUnify fuel).
  Proof.
    induction fuel; simpl; intros; try congruence.
    eapply exprUnify'_sound. eassumption.
  Qed.

End typed.
