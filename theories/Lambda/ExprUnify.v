Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.SubstI3.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprD.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.Lambda.ExprTac.

Require Import FunctionalExtensionality.

Set Implicit Arguments.
Set Strict Implicit.

Section typed.
  Variable subst : Type.
  Variable typ : Type.
  Variable func : Type.
  Variable RType_typ : RType typ.
  Variable RTypeOk_typ : RTypeOk.
  Variable Typ2_arr : Typ2 _ Fun.
  Variable Typ2Ok_arr : Typ2Ok Typ2_arr.
  Variable RSym_func : RSym func.
  Variable RSymOk_func : RSymOk RSym_func.
  Variable Subst_subst : Subst subst (expr typ func).
  Variable SubstUpdate_subst : SubstUpdate subst (expr typ func).
  Variable SubstOk_subst : SubstOk (Expr_expr) Subst_subst.
  Variable SubstUpdateOk_subst
  : @SubstUpdateOk _ _ _ _ Expr_expr _ SubstUpdate_subst _.
  Local Instance Expr_expr : Expr _ (expr typ func) := Expr_expr.

  Local Instance RelDec_Rty ts : RelDec (Rty ts) :=
  { rel_dec := fun a b => match type_cast ts a b with
                            | Some _ => true
                            | None => false
                          end }.
  Variable EqDec_eq_typ : EqDec typ (@eq typ).

  Section nested.
    Variable ts : list Type.

    (** n is the number of binders that we have gone under **)
    Variable exprUnify : forall (tus tvs : tenv typ) (under : nat) (s : subst)
                                (l r : expr typ func), typ -> option subst.

    Fixpoint exprUnify' (us vs : tenv typ) (n : nat) (s : subst)
             (e1 e2 : expr typ func) (t : typ) {struct e1}
    : option subst :=
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
          match typeof_expr ts us vs e1 , typeof_expr ts us vs e2 with
            | Some t1 , Some t2 =>
              if t1 ?[ Rty ts ] t2 then
                typ2_match (fun _ => option subst) ts t1
                           (fun d r =>
                              match exprUnify' us vs n s e1 e2 t1 with
                                | None => None
                                | Some s' =>
                                  exprUnify' us vs n s' e1' e2' d
                              end)
                           None
              else
                None
            | _ , _ => None
          end
        | Abs t1 e1 , Abs t2 e2 =>
          (* t1 = t2 since both terms have the same type *)
          typ2_match (F := Fun) (fun _ => _) ts t
                     (fun _ t =>
                        exprUnify' us (t1 :: vs) (S n) s e1 e2 t)
                     None
        | _ , _ => None
      end%bool.

  End nested.

  Section exprUnify.

    (** Delaying the recursion is probably important **)
    Fixpoint exprUnify (fuel : nat)
             (ts : list Type) (us vs : tenv typ) (under : nat) (s : subst)
             (e1 e2 : expr typ func) (t : typ) : option subst :=
      match fuel with
        | 0 => None
        | S fuel =>
          exprUnify' ts (fun tus tvs => exprUnify fuel ts tus tvs)
                     us vs under s e1 e2 t
      end.
  End exprUnify.

  Existing Instance SubstUpdate_subst.
  Existing Instance SubstOk_subst.

  Definition unify_sound_ind
    (unify : forall ts (us vs : tenv typ) (under : nat) (s : subst)
                    (l r : expr typ func)
                    (t : typ), option subst) : Prop :=
    forall tu tv e1 e2 s s' t tv',
      unify (@nil Type) tu (tv' ++ tv) (length tv') s e1 e2 t = Some s' ->
      WellFormed_subst (expr := expr typ func) s ->
      WellFormed_subst (expr := expr typ func) s' /\
      forall v1 v2 sD,
        exprD' nil tu (tv' ++ tv) t e1 = Some v1 ->
        exprD' nil tu (tv' ++ tv) t e2 = Some v2 ->
        substD tu tv s = Some sD ->
        exists sD',
             substD (expr := expr typ func) tu tv s' = Some sD'
          /\ forall us vs,
               sD' us vs ->
               sD us vs /\
               forall vs',
                 v1 us (hlist_app vs' vs) = v2 us (hlist_app vs' vs).

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

  Lemma handle_set'
  : forall (e0 : expr typ func) (u : uvar) (s s' : subst)
    (Hnot_found : lookup u s = None),
      set u e0 s = Some s' ->
      WellFormed_subst s ->
      WellFormed_subst s' /\
      forall (tu : tenv typ) (tv : list typ)
             (t : typ) (tv' : list typ),
        (forall
            (v1 : _)
            (v2 : hlist (typD nil) tu ->
                    hlist (typD nil) (tv' ++ tv) -> typD nil t)
            (sD : hlist (typD nil) tu -> hlist (typD nil) tv -> Prop),
            exprD' nil tu tv t e0 = Some v1 ->
            exprD' nil tu (tv' ++ tv) t (UVar u) = Some v2 ->
            substD tu tv s = Some sD ->
            exists
              sD' : hlist (typD nil) tu -> hlist (typD nil) tv -> Prop,
              substD tu tv s' = Some sD' /\
              (forall (us : hlist (typD nil) tu)
                      (vs : hlist (typD nil) tv),
                 sD' us vs ->
                 sD us vs /\
                 (forall vs' : hlist (typD nil) tv',
                    v1 us vs = v2 us (hlist_app vs' vs)))).
  Proof.
    intros.
    eapply set_sound in H; eauto.
    forward_reason; split; eauto.
    intros.
    autorewrite with exprD_rw in *; eauto. simpl in *.
    forward; inv_all; subst.
    eapply nth_error_get_hlist_nth_Some in H5.
    forward_reason.
    simpl in *. destruct r.
    specialize (H1 tu tv x _ _ H4 (eq_sym x0) H2).
    forward_reason.
    eexists; split; eauto.
    intros. specialize (H5 _ _ H7).
    forward_reason.
    split; auto. intros.
    rewrite H3.
    match goal with
      | H : ?X = _ |- context [ ?Y ] =>
        change Y with X ; rewrite H
    end. clear.
    rewrite match_eq_sym_eq with (pf := x0) (F := fun x => match x with
                                                             | Some t0 => typD nil t0
                                                             | None => unit
                                                           end).
    reflexivity.
  Qed.

  Lemma handle_set
  : forall (e0 : expr typ func) (u : uvar) (s s' : subst)
           (Hnot_found : lookup u s = None),
      set u e0 s = Some s' ->
      WellFormed_subst s ->
      WellFormed_subst s' /\
      forall (tu : tenv typ) (tv : list typ)
             (t : typ) (tv' : list typ) (e : expr typ func),
        lower 0 (length tv') e = Some e0 ->
        (forall
            (v1
               v2 : hlist (typD nil) tu ->
                    hlist (typD nil) (tv' ++ tv) -> typD nil t)
            (sD : hlist (typD nil) tu -> hlist (typD nil) tv -> Prop),
            exprD' nil tu (tv' ++ tv) t e = Some v1 ->
            exprD' nil tu (tv' ++ tv) t (UVar u) = Some v2 ->
            substD tu tv s = Some sD ->
            exists
              sD' : hlist (typD nil) tu -> hlist (typD nil) tv -> Prop,
              substD tu tv s' = Some sD' /\
              (forall (us : hlist (typD nil) tu)
                      (vs : hlist (typD nil) tv),
                 sD' us vs ->
                 sD us vs /\
                 (forall vs' : hlist (typD nil) tv',
                    v1 us (hlist_app vs' vs) = v2 us (hlist_app vs' vs)))).
  Proof.
    intros.
    eapply set_sound in H; eauto.
    forward_reason; split; eauto.
    intros.
    autorewrite with exprD_rw in *; simpl in *.
    forward; inv_all; subst.
    eapply nth_error_get_hlist_nth_Some in H6.
    forward_reason.
    simpl in *.
    eapply  (@exprD'_lower typ func _ _ RSym_func _ _ _ nil tu nil tv' tv _ t) in H2; eauto.
    simpl in *. destruct r.
    forward_reason.
    specialize (H1 tu tv x _ _ H5 (eq_sym x0) H2).
    forward_reason.
    eexists; split; eauto.
    intros. specialize (H8 _ _ H9).
    forward_reason.
    split; auto. intros.
    specialize (H6 us Hnil vs' vs).
    specialize (H4 us).
    simpl in *.
    rewrite <- H6 in *.
    Cases.rewrite_all_goal.
    change_rewrite H10.
    rewrite match_eq_sym_eq with (pf := x0) (F := fun x => match x with
                                                             | Some t0 => typD nil t0
                                                             | None => unit
                                                           end).
    reflexivity.
  Qed.

  Lemma handle_uvar
  : forall
      (unify : list Type -> tenv typ -> tenv typ ->
               nat -> subst -> expr typ func -> expr typ func -> typ -> option subst),
      unify_sound_ind unify ->
      forall (tu : tenv typ) (tv : list typ) e
             (u : uvar) (s s' : subst) (t : typ) (tv' : list typ),
        match lookup u s with
          | Some e2' =>
            unify nil tu (tv' ++ tv) (length tv') s e
                  (lift 0 (length tv') e2') t
          | None =>
            match lower 0 (length tv') e with
              | Some e1 => set u e1 s
              | None => None
            end
        end = Some s' ->
        WellFormed_subst s ->
        WellFormed_subst s' /\
        (forall
            (v1 v2 : hlist (typD nil) tu ->
                     hlist (typD nil) (tv' ++ tv) -> typD nil t)
            (sD : hlist (typD nil) tu -> hlist (typD nil) tv -> Prop),
            exprD' nil tu (tv' ++ tv) t e = Some v1 ->
            exprD' nil tu (tv' ++ tv) t (UVar u) = Some v2 ->
            substD tu tv s = Some sD ->
            exists
              sD' : hlist (typD nil) tu -> hlist (typD nil) tv -> Prop,
              substD tu tv s' = Some sD' /\
              (forall (us : hlist (typD nil) tu) (vs : hlist (typD nil) tv),
                 sD' us vs ->
                 sD us vs /\
                 (forall vs' : hlist (typD nil) tv',
                    v1 us (hlist_app vs' vs) = v2 us (hlist_app vs' vs)))).
  Proof.
    intros.
    consider (lookup u s); intros.
    { eapply H in H2.
      forward_reason.
      split; eauto; intros.
      assert (exists v2',
                exprD' nil tu (tv' ++ tv) t (lift 0 (length tv') e0) = Some v2'
                /\ forall us vs vs',
                     sD us vs ->
                     v2 us (hlist_app vs' vs) = v2' us (hlist_app vs' vs)).
      { eapply substD_lookup in H0; eauto.
        forward_reason.
        simpl in *.
        autorewrite with exprD_rw in H5; simpl in H5.
        forward. inv_all; subst.
        eapply nth_error_get_hlist_nth_Some in H8.
        simpl in *. forward_reason.
        generalize (@exprD'_lift typ func _ _ _ _ _ _ nil tu e0 nil tv' tv x).
        simpl. change_rewrite H0. clear - x1 x2 H5 H7 EqDec_eq_typ.
        intros; forward.
        assert (t = x) by congruence.
        subst.
        destruct r.
        eexists; split; eauto.
        intros. rewrite H5.
        specialize (H0 us Hnil).
        simpl in *. erewrite H7; eauto.
        rewrite <- H0.
        generalize (x0 us vs).
        change (typD nil x2)
          with (match Some x2 with
                  | Some x => typD nil x
                  | None => unit
                end).
        clear - EqDec_eq_typ.
        destruct x1.
        rewrite (UIP_refl x3).
        reflexivity. }
      forward_reason.
      specialize (H3 _ _ _ H4 H7 H6).
      forward_reason.
      eexists; split; eauto.
      intros. specialize (H9 _ _ H10).
      forward_reason. split; intros; eauto.
      rewrite H11. rewrite H8; eauto. }
    { forward. eapply handle_set in H3; intuition eauto. }
  Qed.

  Lemma handle_uvar'
  : forall
        unify : list Type -> tenv typ -> tenv typ ->
                nat -> subst -> expr typ func -> expr typ func -> typ -> option subst,
        unify_sound_ind unify ->
        forall (tu : tenv typ) (tv : list typ) e
               (u : uvar) (s s' : subst) (t : typ) (tv' : list typ),
          match lookup u s with
            | Some e2' =>
              unify nil tu (tv' ++ tv) (length tv') s
                    (lift 0 (length tv') e2') e t
            | None =>
              match lower 0 (length tv') e with
                | Some e1 => set u e1 s
                | None => None
              end
          end = Some s' ->
          WellFormed_subst s ->
          WellFormed_subst s' /\
          (forall
              (v1 v2 : hlist (typD nil) tu ->
                       hlist (typD nil) (tv' ++ tv) -> typD nil t)
              (sD : hlist (typD nil) tu -> hlist (typD nil) tv -> Prop),
              exprD' nil tu (tv' ++ tv) t (UVar u) = Some v1 ->
              exprD' nil tu (tv' ++ tv) t e = Some v2 ->
              substD tu tv s = Some sD ->
              exists
                sD' : hlist (typD nil) tu -> hlist (typD nil) tv -> Prop,
                substD tu tv s' = Some sD' /\
                (forall (us : hlist (typD nil) tu)
                        (vs : hlist (typD nil) tv),
                   sD' us vs ->
                   sD us vs /\
                   (forall vs' : hlist (typD nil) tv',
                      v1 us (hlist_app vs' vs) = v2 us (hlist_app vs' vs)))).
  Proof.
    intros.
    consider (lookup u s); intros.
    { eapply H in H2.
      forward_reason.
      split; eauto; intros.
      assert (exists v2',
                exprD' nil tu (tv' ++ tv) t (lift 0 (length tv') e0) = Some v2'
                /\ forall us vs vs',
                     sD us vs ->
                     v1 us (hlist_app vs' vs) = v2' us (hlist_app vs' vs)).
      { eapply substD_lookup in H0; eauto.
        forward_reason.
        simpl in *.
        autorewrite with exprD_rw in H4; simpl in H4.
        forward. inv_all; subst.
        eapply nth_error_get_hlist_nth_Some in H8.
        simpl in *. forward_reason.
        generalize (@exprD'_lift typ func _ _ _ _ _ _ nil tu e0 nil tv' tv x).
        simpl. change_rewrite H0. clear - x1 x2 H4 H7 EqDec_eq_typ.
        intros; forward.
        assert (t = x) by congruence.
        subst.
        change_rewrite H.
        eexists; split; eauto.
        intros.
        specialize (H0 us Hnil).
        simpl in *. rewrite <- H0.
        specialize (H7 _ _ H1).
        rewrite H4.
        match goal with
          | H : ?X = _ |- context [ ?Y ] =>
            change Y with X ; rewrite H
        end.
        clear - EqDec_eq_typ.
        destruct x1. destruct r. rewrite (UIP_refl x3). reflexivity. }
      forward_reason.
      specialize (H3 _ _ _ H7 H5 H6).
      forward_reason.
      eexists; split; eauto.
      intros. specialize (H9 _ _ H10).
      forward_reason. split; intros; eauto.
      rewrite H8; eauto. }
    { forward. eapply handle_set in H3; intuition eauto.
      specialize (H5 _ _ _ _ _ H2 _ _ _ H6 H3 H7).
      forward_reason. eexists; split; eauto.
      intros. specialize (H8 _ _ H9). forward_reason; split; eauto. }
  Qed.

  Lemma lookup_lift
  : forall u s e tu tv tv' t sD v1,
      lookup u s = Some e ->
      WellFormed_subst s ->
      substD tu tv s = Some sD ->
      exprD' nil tu (tv' ++ tv) t (UVar u) = Some v1 ->
      exists v1',
        exprD' nil tu (tv' ++ tv) t (lift 0 (length tv') e) = Some v1' /\
        forall us vs vs',
          sD us vs ->
          v1 us (hlist_app vs' vs) = v1' us (hlist_app vs' vs).
  Proof.
    intros.
    eapply substD_lookup in H; eauto.
    simpl in *. forward_reason.
    generalize (@exprD'_lift typ func RType_typ Typ2_arr _ _ _ _
                             nil tu e nil tv' tv x).
    simpl. change_rewrite H.
    intros; forward.
    autorewrite with exprD_rw in H2. simpl in H2.
    forward.
    inv_all. subst. destruct r.
    eapply nth_error_get_hlist_nth_Some in H6. simpl in H6.
    forward_reason.
    assert (x2 = x) by congruence.
    subst.
    eexists; split; eauto.
    intros.
    unfold Rcast_val,Rcast,Relim; simpl.
    rewrite H2; clear H2.
    eapply H3 in H6. change_rewrite H6.
    specialize (H5 us Hnil vs' vs). simpl in H5.
    change_rewrite H5.
    match goal with
      | |- match _ with eq_refl => match _ with eq_refl => ?X end end = ?Y =>
        change Y with X ; generalize X
    end.
    clear - EqDec_eq_typ.
    destruct x1.
    rewrite (UIP_refl x3). reflexivity.
  Qed.

  Lemma exprUnify'_sound
  : forall unify,
      unify_sound_ind unify ->
      unify_sound_ind (fun ts => exprUnify' ts (unify ts)).
  Proof.
    Opaque rel_dec.
    red. induction e1; simpl; intros.
    { destruct e2; try solve [ congruence | eapply handle_uvar; eauto ].
      { consider (EqNat.beq_nat v v0); intros; try congruence.
        inv_all; subst. intuition.
        eexists; split; eauto.
        intros; split; eauto.
        change_rewrite H0 in H2. inv_all; subst; reflexivity. } }
    { destruct e2; try solve [ congruence | eapply handle_uvar; eauto ].
      { consider (sym_eqb f f0); try congruence; intros.
        destruct b; try congruence. inv_all; subst.
        generalize (@sym_eqbOk _ _ _ _ RSymOk_func f f0).
        rewrite H0. intros; subst. intuition.
        eexists; split; eauto. change_rewrite H3 in H2.
        intuition. congruence. } }
    { destruct e2; try solve [ congruence | eapply handle_uvar; eauto ].
      { forward.
        match goal with
          | H : typ2_match _ ?ts ?t _ _ = _ |- _ =>
            arrow_case ts t; try congruence
        end.
        rewrite eq_Const_eq in H4.
        red in x1; red in H3. subst. subst.
        unfold Relim in H4.
        forward.
        specialize (IHe1_1 e2_1 s s0 (typ2 x x0) tv').
        specialize (IHe1_2 e2_2 s0 s' x tv').
        forward_reason.
        split; eauto. intros.
        autorewrite with exprD_rw in *; simpl in *.
        forward. inv_all; subst.
        forward_exprD.
        repeat match goal with
                 | H : _ |- _ => rewrite H in *
               end.
        specialize (H7 _ _ _ eq_refl eq_refl eq_refl).
        forward_reason.
        specialize (H9 _ _ _ eq_refl eq_refl H7).
        forward_reason.
        eexists; split; eauto. intros.
        eapply H18 in H20; clear H18; forward_reason.
        eapply H15 in H18; clear H15; forward_reason.
        split; eauto. intros.
        unfold Open_App.
        unfold OpenT, ResType.OpenT.
        repeat first [ rewrite eq_Const_eq | rewrite eq_Arr_eq ].
        Cases.rewrite_all_goal. reflexivity. } }
    { destruct e2; try solve [ congruence | eapply handle_uvar; eauto ].
      { forward. subst.
        match goal with
          | H : typ2_match _ ?ts ?t _ _ = _ |- _ =>
            arrow_case ts t; try congruence
        end.
        unfold Relim in H0.
        rewrite eq_Const_eq in H0.
        red in x1. subst.
        rewrite eq_Const_eq in H0.
        specialize (IHe1 e2 s s' _ (t :: tv') H0 H1). simpl in *.
        forward_reason.
        split; eauto; intros.
        autorewrite with exprD_rw in *; simpl in *; forward.
        repeat rewrite typ2_match_zeta in * by eauto.
        repeat rewrite eq_option_eq in *.
        forward.
        red in r; red in r0. subst. inv_all; subst.
        specialize (H12 _ _ _ eq_refl H9 H7).
        forward_reason.
        eexists; split; eauto. intros.
        eapply H10 in H11; clear H10. forward_reason.
        split; auto. intros.
        unfold OpenT, ResType.OpenT.
        repeat first [ rewrite eq_Const_eq | rewrite eq_Arr_eq ].
        eapply match_eq_match_eq with (pf := eq_sym (typ2_cast nil t x0)) (F := fun x => x).
        eapply functional_extensionality; intros.
        apply (H11 (Hcons x1 vs')). } }
    { destruct e2; try solve [ eapply handle_uvar'; eauto ].
      { consider (EqNat.beq_nat u u0); intros; inv_all; subst.
        { split; eauto; intros.
          autorewrite with exprD_rw in *; simpl in *.
          forward; inv_all; subst.
          eexists; split; eauto.
          intros; split; auto.
          destruct r0. destruct r.
          change_rewrite H7 in H4.
          inv_all. subst. reflexivity. }
        { consider (lookup u s); consider (lookup u0 s); intros.
          { eapply H in H4.
            forward_reason.
            split; eauto. intros.
            eapply lookup_lift in H2; eauto.
            eapply lookup_lift in H3; eauto.
            forward_reason.
            specialize (H5 _ _ _ H3 H2 H8).
            forward_reason.
            eexists; split; eauto. intros.
            eapply H11 in H12. forward_reason; split; auto.
            intros. rewrite H9; eauto. rewrite H10; eauto. }
          { eapply handle_set' in H4; eauto. clear H2.
            forward_reason; split; eauto. intros.
            eapply substD_lookup in H3; eauto.
            forward_reason.
            simpl in *.
            autorewrite with exprD_rw in H5; simpl in H5.
            forward; inv_all; subst.
            eapply nth_error_get_hlist_nth_Some in H9.
            simpl in H9. forward_reason.
            assert (x = t) by congruence. subst.
            specialize (H4 _ _ _ _ _ _ _ H3 H6 H7).
            forward_reason.
            eexists; split; eauto.
            intros. specialize (H9 _ _ H11).
            forward_reason. split; eauto.
            intros.
            rewrite H5. rewrite <- H12.
            rewrite (H8 _ vs); eauto.
            clear - EqDec_eq_typ.
            generalize (x0 us vs).
            change (typD nil t)
              with (match Some t with
                      | Some t => typD nil t
                      | None => unit
                    end).
            destruct x1.
            destruct r.
            rewrite (UIP_refl x3). reflexivity. }
          { eapply handle_set' in H4; eauto.
            clear H3.
            forward_reason; split; eauto. intros.
            eapply substD_lookup in H2; eauto.
            forward_reason.
            simpl in *.
            autorewrite with exprD_rw in H6; simpl in H6.
            forward; inv_all; subst.
            eapply nth_error_get_hlist_nth_Some in H9.
            simpl in H9. forward_reason.
            assert (x = t) by congruence. subst.
            specialize (H4 _ _ _ _ _ _ _ H2 H5 H7).
            forward_reason.
            eexists; split; eauto.
            intros. specialize (H9 _ _ H11).
            forward_reason. split; eauto.
            intros.
            rewrite H6. rewrite <- H12.
            rewrite (H8 _ vs); eauto.
            clear - EqDec_eq_typ.
            generalize (x0 us vs).
            change (typD nil t)
              with (match Some t with
                      | Some t => typD nil t
                      | None => unit
                    end).
            destruct r.
            destruct x1. uip_all. reflexivity. }
          { consider (set u (UVar u0) s); intros; inv_all; subst.
            { eapply handle_uvar'; eauto.
              rewrite H3. simpl. assumption. }
            { eapply handle_uvar; eauto.
              rewrite H2. simpl. assumption. } } } } }
  Qed.

  Theorem exprUnify_sound : forall fuel, unify_sound (exprUnify fuel).
  Proof.
    induction fuel; simpl; intros; try congruence.
    eapply exprUnify'_sound. eassumption.
  Qed.

End typed.
