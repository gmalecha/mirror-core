Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.Lambda.ExprUnify_common.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.Lambda.ExprTac.
Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.Util.Compat.

Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Set Strict Implicit.

Section typed.
  Variable subst : Type.
  Variable typ : Type.
  Variable func : Type.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {RSym_func : RSym func}.
  Context {RSymOk_func : RSymOk RSym_func}.
  Local Existing Instance Expr_expr.
  Context {Typ2_arr : Typ2 _ RFun}.
  Context {Typ2Ok_arr : Typ2Ok Typ2_arr}.

  Context {Subst_subst : Subst subst (expr typ func)}.
  Context {SubstUpdate_subst : SubstUpdate subst (expr typ func)}.
  Context {SubstOk_subst : SubstOk subst typ (expr typ func)}.
  Context {SubstUpdateOk_subst : SubstUpdateOk subst typ (expr typ func)}.

  Local Instance RelDec_Rty : RelDec Rty :=
  { rel_dec := fun a b => match type_cast a b with
                            | Some _ => true
                            | None => false
                          end }.

  Section nested.
    (** n is the number of binders that we have gone under **)
    Variable exprUnify : forall (tus tvs : tenv typ) (under : nat)
                                (l r : expr typ func), typ -> subst -> option subst.

    Fixpoint exprUnify' (us vs : tenv typ) (n : nat)
             (e1 e2 : expr typ func) (t : typ) (s : subst) {struct e1}
    : option subst :=
      match e1 , e2 with
        | UVar u1 , UVar u2 =>
          if EqNat.beq_nat u1 u2 then Some s
          else
            match subst_lookup u1 s , subst_lookup u2 s with
              | None , None =>
                match subst_set u1 (UVar u2) s with
                  | None =>
                    subst_set u2 (UVar u1) s
                  | Some s => Some s
                end
              | Some e1' , None =>
                subst_set u2 e1' s
              | None , Some e2' =>
                subst_set u1 e2' s
              | Some e1' , Some e2' =>
                exprUnify us vs n (lift 0 n e1') (lift 0 n e2') t s
            end
        | UVar u1 , _ =>
          match subst_lookup u1 s with
            | None =>
              match lower 0 n e2 with
                | None => None
                | Some e2 => subst_set u1 e2 s
              end
            | Some e1' => exprUnify us vs n (lift 0 n e1') e2 t s
          end
        | _ , UVar u2 =>
          match subst_lookup u2 s with
            | None =>
              match lower 0 n e1 with
                | None => None
                | Some e1 => subst_set u2 e1 s
              end
            | Some e2' => exprUnify us vs n e1 (lift 0 n e2') t s
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
            | Some t1 , Some t2 =>
              if t1 ?[ Rty ] t2 then
                typ2_match (fun _ => option subst) t1
                           (fun d r =>
                              match exprUnify' us vs n e1 e2 t1 s with
                                | None => None
                                | Some s' =>
                                  exprUnify' us vs n e1' e2' d s'
                              end)
                           None
              else
                None
            | _ , _ => None
          end
        | Abs t1 e1 , Abs t2 e2 =>
          (* t1 = t2 since both terms have the same type *)
          typ2_match (F:=RFun) (fun _ => _) t
                     (fun _ t =>
                        exprUnify' us (t1 :: vs) (S n) e1 e2 t s)
                     None
        | _ , _ => None
      end%bool.

  End nested.

  Section exprUnify.

    (** Delaying the recursion is probably important **)
    Fixpoint exprUnify (fuel : nat)
             (us vs : tenv typ) (under : nat)
             (e1 e2 : expr typ func) (t : typ) (s : subst) : option subst :=
      match fuel with
        | 0 => None
        | S fuel =>
          exprUnify' (fun tus tvs => exprUnify fuel tus tvs)
                     us vs under e1 e2 t s
      end.
  End exprUnify.

  Existing Instance SubstUpdate_subst.
  Existing Instance SubstOk_subst.

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

  Lemma exprUnify'_sound
  : forall unify,
      unify_sound_ind unify ->
      unify_sound_ind (exprUnify' unify).
  Proof.
    Opaque rel_dec.
    red. induction e1; simpl; intros.
    { destruct e2; try solve [ congruence | eapply handle_uvar; eauto ].
      { consider (EqNat.beq_nat v v0); intros; try congruence.
        inv_all; subst. split. assumption. intros.
        eexists; split; eauto. reflexivity.
        intros; split; eauto.
        change_rewrite H0 in H2. inv_all; subst.
        tauto. } }
    { destruct e2; try solve [ congruence | eapply handle_uvar; eauto ].
      { consider (sym_eqb f f0); try congruence; intros.
        destruct b; try congruence. inv_all; subst.
        generalize (@sym_eqbOk _ _ _ _ RSymOk_func f f0).
        rewrite H0. intros; subst.
        split; [ assumption | ].
        eexists; split; eauto. reflexivity.
        split; eauto.
        change_rewrite H3 in H2.
        intuition. congruence. } }
    { destruct e2; try solve [ congruence | eapply handle_uvar; eauto ].
      { forward.
        match goal with
          | H : typ2_match _ ?t _ _ = _ |- _ =>
            arrow_case t; try congruence
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
        specialize (H7 _ _ _ H16 H13 H12).
        forward_reason.
        specialize (H9 _ _ _ H17 H14 H15).
        forward_reason.
        eexists; split; eauto.
        { etransitivity; eauto. }
        split. eauto.
        intros.
        repeat match goal with
                 | H : _ _ _ , H' : _ |- _ =>
                   specialize (H' _ _ H); forward_reason
               end.
        split; eauto.
        unfold AbsAppI.exprT_App.
        autorewrite_with_eq_rw. intros.
        Cases.rewrite_all_goal. reflexivity. } }
    { destruct e2; try solve [ congruence | eapply handle_uvar; eauto ].
      { forward. subst.
        arrow_case_any; try congruence.
        unfold Relim in H0.
        rewrite eq_Const_eq in H0.
        red in x1. subst.
        rewrite eq_Const_eq in H0.
        specialize (IHe1 e2 s s' _ (t :: tv') H0 H1). simpl in *.
        forward_reason.
        split; eauto; intros.
        autorewrite with exprD_rw in *; simpl in *; forward.
        repeat rewrite typ2_match_iota in * by eauto.
        repeat rewrite eq_option_eq in *.
        forward.
        red in r; red in r0. subst. inv_all; subst.
        specialize (H12 _ _ _ eq_refl H9 H7).
        forward_reason.
        eexists; split; eauto. intros.
        split; eauto. intros.
        eapply H11 in H12; clear H11. forward_reason.
        split; auto. intros.
        autorewrite_with_eq_rw.
        eapply match_eq_match_eq with (pf := eq_sym (typ2_cast t x0)) (F := fun x => x).
        eapply functional_extensionality; intros.
        apply (H12 (Hcons x1 vs')). } }
    { destruct e2; try solve [ eapply handle_uvar'; eauto ].
      { consider (EqNat.beq_nat u u0); intros; inv_all; subst.
        { split; eauto; intros.
          change_rewrite H0 in H2. inv_all. subst.
          eexists. split; [ reflexivity | eauto ]. }
        { consider (subst_lookup u s); consider (subst_lookup u0 s); intros.
          { eapply H in H4.
            forward_reason.
            split; eauto. intros.
            eapply lookup_lift in H2; eauto.
            eapply lookup_lift in H3; eauto.
            forward_reason.
            specialize (H5 _ _ _ H3 H2 H8).
            forward_reason.
            eexists; split; eauto.
            split; eauto. intros.
            eapply H12 in H13. forward_reason; split; auto.
            intros. rewrite H9; eauto. rewrite H10; eauto. }
          { eapply handle_set in H4; eauto. clear H2.
            forward_reason; split; eauto. intros.
            eapply substD_lookup in H3; eauto.
            forward_reason.
            simpl in *.
            autorewrite with exprD_rw in H5; simpl in H5.
            change_rewrite H3 in H5.
            forwardy; inv_all; subst.
            destruct y.
            specialize (H4 _ _ _ _ _ _ _ H8 H6 H7).
            forward_reason.
            eexists; split; eauto.
            split; eauto.
            intros. specialize (H11 _ _ H12).
            forward_reason. split; eauto.
            intros.
            etransitivity. eapply H9; eauto.
            eauto. }
          { eapply handle_set in H4; eauto.
            clear H3.
            forward_reason; split; eauto. intros.
            eapply substD_lookup in H2; eauto.
            forward_reason.
            simpl in *.
            autorewrite with exprD_rw in H6; simpl in H6.
            change_rewrite H2 in H6.
            forwardy; inv_all; subst.
            destruct y.
            specialize (H4 _ _ _ _ _ _ _ H8 H5 H7).
            forward_reason.
            eexists; split; eauto. split; eauto.
            intros. specialize (H11 _ _ H12).
            forward_reason. split; eauto.
            etransitivity; [ symmetry; eapply H13 | symmetry ; eapply H9 ].
            assumption. }
          { consider (subst_set u (UVar u0) s); intros; inv_all; subst.
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
