Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprUnify_common.
Require Import MirrorCore.Lambda.ExprD.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.Lambda.ExprTac.
Require Import MirrorCore.Util.Forwardy.

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
  Local Existing Instance Expr_expr.

  Local Instance RelDec_Rty : RelDec Rty :=
  { rel_dec := fun a b => match type_cast a b with
                            | Some _ => true
                            | None => false
                          end }.

  Instance RelDec_eq_expr : RelDec (@eq (expr typ func)). Admitted.

  Section nested.
    (** n is the number of binders that we have gone under **)
    Variable exprUnify : forall (tus : tenv (ctyp typ)) (tvs : tenv typ)
                                (l r : expr typ func), typ -> subst -> option subst.

    Definition substList (e : expr typ func) (es : list (expr typ func))
    : expr typ func.
    Admitted.

    Fixpoint find (e : expr typ func) (acc : nat) (es : list (expr typ func)) : option nat :=
      match es with
        | nil => None
        | e' :: es' =>
          if e ?[ eq ] e' then Some acc
          else find e (S acc) es'
      end.

    Axiom instantiate : subst -> expr typ func -> expr typ func.

    Fixpoint patterns (es : list (expr typ func)) (s : subst)
             (e : expr typ func) {struct e}
    : option (expr typ func).
      refine
        match e with
          | Inj i => Some (Inj i)
          | UVar u es' =>
            match mapT_list (F:=option) (patterns es s) es' with
              | None => None (** I could do something here **)
              | Some es'' => Some (UVar u es'')
            end
          | App e1 e2 =>
            match patterns es s e1
                , patterns es s e2 with
              | Some e1' , Some e2' => Some (App e1' e2')
              | _ , _ => None
            end
          | _ =>
            (** This is the only case that I expect to happen **)
            match find e 0 es with
              | None => None
              | Some v' => Some (Var v')
            end
        end.
    Defined.

    Definition try_set
               (u : uvar) (args1 : list (expr typ func))
               (e2 : expr typ func)
               (s : subst) : option subst :=
      match patterns args1 s e2 with
        | None => None
        | Some e => set u e s
      end.

    Fixpoint fold_left3 {A B C} (f : C -> A -> A -> B -> option B) (t : list C)
             (x y : list A) (s : B)
    : option B :=
      match t , x , y with
        | nil , nil , nil => Some s
        | t :: ts , x :: xs , y :: ys =>
          match f t x y s with
            | None => None
            | Some s => fold_left3 f ts xs ys s
          end
        | _ , _ , _ => None
      end.

    Fixpoint exprUnify' (us : tenv (ctyp typ)) (vs : tenv typ)
             (e1 e2 : expr typ func) (t : typ) (s : subst) {struct e1}
    : option subst.
    refine
      match e1 , e2 with
        | UVar u1 es1 , UVar u2 es2 =>
          if EqNat.beq_nat u1 u2 then
            match nth_error us u1 with
              | Some ct =>
                fold_left3 (fun t e1 e2 s =>
                              exprUnify us vs e1 e2 t s)
                           ct.(cctx) es1 es2 s
              | None => None
            end
          else
            match lookup u1 s , lookup u2 s with
              | None , None =>
                match set u1 e2 s with
                  | None => set u2 e1 s
                  | Some s => Some s
                end
              | Some e1' , None =>
                try_set u2 es2 e1' s
              | None , Some e2' =>
                try_set u1 es1 e2' s
              | Some e1' , Some e2' =>
                exprUnify us vs (substList e1' es1) (substList e2' es2) t s
            end
        | UVar u1 es1 , _ =>
          match lookup u1 s with
            | None =>
              try_set u1 es1 e2 s
            | Some e1' => exprUnify us vs (substList e1' es1) e2 t s
          end
        | _ , UVar u2 es2 =>
          match lookup u2 s with
            | None =>
              try_set u2 es2 e1 s
            | Some e2' => exprUnify us vs e1 (substList e2' es2) t s
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
                              match exprUnify' us vs e1 e2 t1 s with
                                | None => None
                                | Some s' =>
                                  exprUnify' us vs e1' e2' d s'
                              end)
                           None
              else
                None
            | _ , _ => None
          end
        | Abs t1 e1 , Abs t2 e2 =>
          (* t1 = t2 since both terms have the same type *)
          typ2_match (F := Fun) (fun _ => _) t
                     (fun _ t =>
                        exprUnify' us (t1 :: vs) e1 e2 t s)
                     None
        | _ , _ => None
      end%bool.
    Defined.

  End nested.

  Section exprUnify.

    (** Delaying the recursion is probably important **)
    Fixpoint exprUnify (fuel : nat)
             (us : tenv (ctyp typ)) (vs : tenv typ)
             (e1 e2 : expr typ func) (t : typ) (s : subst) : option subst :=
      match fuel with
        | 0 => None
        | S fuel =>
          exprUnify' (fun tus tvs => exprUnify fuel tus tvs)
                     us vs e1 e2 t s
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
      unify_sound_ind _ unify ->
      unify_sound_ind _ (exprUnify' unify).
  Proof.
    Opaque rel_dec.
(*
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
        arrow_case_any; try congruence.
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
        eapply match_eq_match_eq with (pf := eq_sym (typ2_cast t x0)) (F := fun x => x).
        eapply functional_extensionality; intros.
        apply (H11 (Hcons x1 vs')). } }
    { destruct e2; try solve [ eapply handle_uvar'; eauto ].
      { consider (EqNat.beq_nat u u0); intros; inv_all; subst.
        { split; eauto; intros.
          change_rewrite H0 in H2. inv_all. subst.
          eauto. }
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
            intros. specialize (H10 _ _ H11).
            forward_reason. split; eauto.
            intros.
            etransitivity; [ eapply H9 | eapply H12 ]; eassumption. }
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
            eexists; split; eauto.
            intros. specialize (H10 _ _ H11).
            forward_reason. split; eauto.
            etransitivity; [ symmetry; eapply H12 | symmetry ; eapply H9 ].
            assumption. }
          { consider (set u (UVar u0) s); intros; inv_all; subst.
            { eapply handle_uvar'; eauto.
              rewrite H3. simpl. assumption. }
            { eapply handle_uvar; eauto.
              rewrite H2. simpl. assumption. } } } } }
*)
    admit.
  Qed.

  Theorem exprUnify_sound : forall fuel, unify_sound _ (exprUnify fuel).
  Proof.
    induction fuel; simpl; intros; try congruence.
    eapply exprUnify'_sound. eassumption.
  Qed.

End typed.
