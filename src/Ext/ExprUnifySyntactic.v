Require Import List.
Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.Prover.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.Subst.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.ExprCore.
Require Import MirrorCore.Ext.ExprT.
Require Import MirrorCore.Ext.ExprD.
Require Import MirrorCore.Ext.ExprLift.

Set Implicit Arguments.
Set Strict Implicit.

Section typed.
  Variable subst : Type.
  Variable types : Types.types.
  Variable funcs : functions types.
  Variable Subst_subst : Subst subst expr.
  Variable SubstOk_subst : SubstOk (Expr_expr funcs) Subst_subst.

  Section nested.
    Variable tfs : tfunctions.

    (** n is the number of binders that we have gone under **)
  Variable exprUnify : forall (us vs : tenv typ) (under : nat) (s : subst) (l r : expr), typ -> option subst.

  Fixpoint exprUnify' (us vs : tenv typ) (n : nat) (s : subst) (e1 e2 : expr) (t : typ) {struct e1}
  : option subst.
  refine (
    match e1 , e2 with
      | UVar u1 , UVar u2 =>
        if EqNat.beq_nat u1 u2 then Some s
        else
          match Subst.set u1 (UVar u2) s with
            | None => Subst.set u2 (UVar u1) s
            | x => x
          end
      | UVar u1 , _ =>
        match Subst.lookup u1 s with
          | None =>
            match lower n n e2 with
              | None => None
              | Some e2 => Subst.set u1 e2 s
            end
          | Some e1' => exprUnify us vs n s (lift 0 n e1') e2 t
        end
      | _ , UVar u2 =>
        match Subst.lookup u2 s with
          | None =>
            match lower n n e1 with
              | None => None
              | Some e1 => Subst.set u2 e1 s
            end
          | Some e2' => exprUnify us vs n s e1 (lift 0 n e2') t
        end
      | Var v1 , Var v2 =>
        if EqNat.beq_nat v1 v2 then Some s else None
      | Func f1 ts1 , Func f2 fs2 =>
        if EqNat.beq_nat f1 f2 then Some s else None
      | App e1 e1' , App e2 e2' =>
        (** TODO: This isn't correct because the type of [e1] might be
         ** different than the type of [e2].
         ** - In order to call the type checker, I need the type environment.
         **)
        match typeof_expr tfs us vs e1 , typeof_expr tfs us vs e2 with
          | Some (tvArr l r) , Some (tvArr l' r') =>
            if l ?[ eq ] l' && r ?[ eq ] r' && t ?[ eq ] r then
              match exprUnify' us vs n s e1 e2 (tvArr l t) with
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
          | tvArr _ t =>
            exprUnify' us (t1 :: vs) (S n) s e1 e2 t
          | _ => None
        end
      | Not e1 , Not e2 =>
        exprUnify' us vs n s e1 e2 tvProp
      | Equal t' e1 e2 , Equal t'' e1' e2' =>
        if t' ?[ eq ] t'' then
          match exprUnify' us vs n s e1 e1' t' with
            | None => None
            | Some s' => exprUnify' us vs n s' e2 e2' t'
          end
        else None
      | _ , _ => None
    end)%bool.
  Defined.
  End nested.

  Section exprUnify.
    Variable tfs : tfunctions.

    Fixpoint exprUnify (fuel : nat) (us vs : tenv typ) (under : nat) (s : subst) (e1 e2 : expr) (t : typ) 
    : option subst :=
      match fuel with
        | 0 => None
        | S fuel =>
          exprUnify' tfs (exprUnify fuel) us vs under s e1 e2 t
      end.
  End exprUnify.

  Require Import ExtLib.Tactics.Consider.
  Require Import ExtLib.Tactics.Injection.

  Definition unify_sound
             (unify : forall (us vs : tenv typ) (under : nat) (s : subst) (l r : expr) (t : typ), option subst) : Prop :=
    forall e1 e2 under s s' t u v,
    exprD funcs u v e1 t <> None ->
    exprD funcs u v e2 t <> None ->
    unify (typeof_env u) (typeof_env v) under s e1 e2 t = Some s' ->
    substD (SubstOk := SubstOk_subst) u v s' ->
       exprD funcs u v e1 t = exprD funcs u v e2 t
    /\ substD (SubstOk := SubstOk_subst) u v s.

  Definition Safe (u v : env (typD types)) e t : Prop :=
    WellTyped_expr (typeof_funcs funcs) (typeof_env u) (typeof_env v) e t.

  Definition unify_sound_ind
             (unify : forall (us vs : tenv typ) (under : nat) (s : subst) (l r : expr) (t : typ), option subst) : Prop :=
    forall e1 e2 under s s' t u v,
      Safe u v e1 t ->
      Safe u v e2 t ->
      WellTyped_subst (SubstOk := SubstOk_subst) (typeof_env u) (typeof_env v) s ->
      unify (typeof_env u) (typeof_env v) under s e1 e2 t = Some s' ->
         WellTyped_subst (SubstOk := SubstOk_subst) (typeof_env u) (typeof_env v) s'
      /\ (substD (SubstOk := SubstOk_subst) u v s' ->
             exprD funcs u v e1 t = exprD funcs u v e2 t
          /\ substD (SubstOk := SubstOk_subst) u v s).

  Definition unify_sound_ind'
    (unify : forall (us vs : tenv typ) (under : nat) (s : subst) (l r : expr) (t : typ), option subst) : Prop :=
    forall e1 e2 s s' t u v v',
      Safe u v e1 t ->
      Safe u v e2 t ->
      WellTyped_subst (SubstOk := SubstOk_subst) (typeof_env u) (typeof_env v) s ->
      unify (typeof_env u) (typeof_env (v' ++ v)) (length v') s e1 e2 t = Some s' ->
         WellTyped_subst (SubstOk := SubstOk_subst) (typeof_env u) (typeof_env v) s'
      /\ (substD (SubstOk := SubstOk_subst) u v s' ->
             exprD funcs u (v' ++ v) e1 t = exprD funcs u (v' ++ v) e2 t
          /\ substD (SubstOk := SubstOk_subst) u v s).

  Lemma WellTyped_subst_lookup_Safe : forall u v s uv e t,
    WellTyped_subst (SubstOk := SubstOk_subst) (typeof_env u) (typeof_env v) s ->
    nth_error (typeof_env u) uv = Some t ->
    lookup uv s = Some e ->
    Safe u v e t.
  Proof.
  Admitted.

  Lemma WellTyped_subst_set : forall uv e s s' (u v : tenv typ),
                                WellTyped_subst (SubstOk := SubstOk_subst) u v s ->
                                set uv e s = Some s' ->
                                WellTyped_subst (SubstOk := SubstOk_subst) u v s'.
  Admitted.
  Lemma substD_set : forall uv e s s' u v,
                       substD (SubstOk := SubstOk_subst) u v s' ->
                       set uv e s = Some s' ->
                       substD (SubstOk := SubstOk_subst) u v s /\
                       (forall tv, nth_error u uv = Some tv ->
                                   exprD funcs u v e (projT1 tv) = Some (projT2 tv)).
  Admitted.
  Lemma Safe_UVar : forall u v u0 t,
                      Safe u v (UVar u0) t ->
                      nth_error (typeof_env u) u0 = Some t.
  Proof.
    clear; unfold Safe; simpl; intros.
    rewrite WellTyped_expr_UVar in H. auto.
  Qed.

  Lemma exprUnify'_sound : forall unify,
                             unify_sound_ind' unify ->
                             unify_sound_ind' (exprUnify' (typeof_funcs funcs) unify).
  Proof.
    Opaque rel_dec.
    red. induction e1; simpl; intros.
    { destruct e2; try congruence.
      { consider (EqNat.beq_nat v v1); intros; try congruence. 
        inv_all; subst. intuition. }
      { generalize dependent (Var v); intros.
        consider (lookup u0 s); intros.
        { eapply H in H4; eauto using WellTyped_subst_lookup_Safe.
          destruct H4. intuition.
          autorewrite with exprD_rw.
          unfold lookupAs. eapply substD_lookup in H8; eauto.
          destruct H8. destruct x. destruct H7. simpl in *. rewrite H7.
          assert (x = t) by admit.
          subst. rewrite typ_cast_typ_refl. rewrite H5. eauto. }
        { consider (lower under under e); try congruence; intros.
          split; eauto using WellTyped_subst_set. intros.
          autorewrite with exprD_rw. unfold lookupAs.

          eapply substD_set in H5; eauto. intuition.
          eapply Safe_UVar in H1.
          unfold typeof_env in *.
          Require Import ExtLib.Data.ListNth.
          erewrite nth_error_map in H1.
          destruct (nth_error u u0); try congruence.
          destruct s0. simpl in *; inv_all; subst.
          specialize (H8 _ eq_refl). simpl in *.
          rewrite typ_cast_typ_refl. 


  Lemma exprUnify'_sound : forall unify,
                             unify_sound unify ->
                             unify_sound (exprUnify' (typeof_funcs funcs) unify).
  Proof.
    Opaque rel_dec.
    red. induction e1; simpl; intros.
    { destruct e2; try congruence.
      { consider (EqNat.beq_nat v v1); intros; try congruence. subst.
        inv_all; subst. intuition. }
      { generalize dependent (Var v); intros.
        consider (lookup u0 s); intros.
        { eapply H in H4; eauto.
          Focus 2.
          specialize (H4 H3). destruct H4.
          eapply substD_lookup in H2; eauto.
          destruct H2. simpl in *. destruct H2.
          rewrite H4. autorewrite with exprD_rw.
          unfold lookupAs. rewrite H2. destruct x; simpl in *.
          assert (x = t) by admit.
          subst. rewrite typ_cast_typ_refl. intuition.
          
          destruct 


admit. } }
    { destruct e2; try congruence.
      { consider (EqNat.beq_nat f f0); try congruence; intros; subst.
        inv_all; subst. split; auto.
        admit. }
      { admit. } }
    { destruct e2; try congruence.
      { autorewrite with exprD_rw in *.
        repeat match goal with
                 | H : match ?X with _ => _ end = _ |- _ =>
                   (consider X; try congruence); [ intros ]
                 | H : not (match ?X with _ => _ end = _) |- _ =>
                   (consider X; try congruence); [ intros ]
                 | H : _ /\ _ |- _ => destruct H
                 | H : not (Some _ = None) |- _ => clear H
               end.
        subst.
        eapply IHe1_2 in H9; try congruence; eauto.
        destruct H9.
        eapply IHe1_1 in H8; try congruence; eauto.
        destruct H8.
        intuition. f_equal. rewrite H6 in *.
        rewrite H4 in H7.
        rewrite typ_cast_typ_refl in *.
        rewrite H10 in *. rewrite H0 in *.
        inv_all; subst.
        reflexivity. }
      { admit. } }
    { destruct e2; try congruence.
      { destruct t0; try congruence.
        assert (t = t0_1) by admit.
        assert (t1 = t0_1) by admit.
        subst.
        consider (exprD funcs u v (Abs t0_1 e1) (tvArr t0_1 t0_2)); try congruence; intros.
        consider (exprD funcs u v (Abs t0_1 e2) (tvArr t0_1 t0_2)); try congruence; intros.
        admit. }
      { admit. } }
    { admit. }
    { destruct e2; try congruence.
      { admit. }
      { autorewrite with exprD_rw in *.
        repeat match goal with
                 | H : match ?X with _ => _ end = _ |- _ =>
                   (consider X; try congruence); [ intros ]
                 | H : not (match ?X with _ => _ end = _) |- _ =>
                   (consider X; try intuition congruence); [ intros ]
                 | H : _ /\ _ |- _ => destruct H
                 | H : not (Some _ = None) |- _ => clear H
               end.
        subst.
        eapply IHe1_2 in H5; try congruence; eauto. destruct H5.
        eapply IHe1_1 in H4; try congruence; eauto. destruct H4.
        rewrite H1 in *. rewrite H9 in *. rewrite H7 in *. rewrite H6 in *.
        inv_all. subst. intuition. } }
    { destruct e2; try congruence.
      { admit. }
      { autorewrite with exprD_rw in *.
        repeat match goal with
                 | H : match ?X with _ => _ end = _ |- _ =>
                   (consider X; try congruence); [ intros ]
                 | H : not (match ?X with _ => _ end = _) |- _ =>
                   (consider X; try intuition congruence); [ intros ]
                 | H : _ /\ _ |- _ => destruct H
                 | H : not (Some _ = None) |- _ => clear H
               end.
        subst. eapply IHe1 in H2; try congruence. intuition.
        rewrite H4 in *. rewrite H1 in *. inv_all; subst. auto. } }
  Qed.

  Theorem exprUnify_sound : forall fuel, unify_sound (exprUnify (typeof_funcs funcs) fuel).
  Proof.
    induction fuel; simpl; intros; try congruence.
    eapply exprUnify'_sound. eassumption.
  Qed.

End typed.

(*
  Definition exprUnify : unifier ts.
  red.
  refine (fun Subst Subst_Subst Prover Facts =>
    (** TODO: Use the prover in places where I return [None] **)
    (fix exprUnify (n : nat) : Subst -> expr ts -> expr ts -> option Subst :=
      match n with
        | 0 => fun _ _ _ => None
        | S n =>
          (fix unify s (e1 e2 : expr ts) {struct e1} : option Subst :=
            match e1 , e2 with
              | Const t1 v1 , Const t2 v2 =>
                match const_seqb ts _ t1 t2 v1 v2 with
                  | Some true => Some s
                  | _ => None
                end
              | UVar u1 , UVar u2 =>
                if EqNat.beq_nat u1 u2 then Some s
                else
                  match Subst.set _ _ u1 (UVar u2) s with
                    | None => Subst.set _ _ u2 (UVar u1) s
                    | x => x
                  end
              | UVar u1 , _ =>
                match Subst.lookup _ _ u1 s with
                  | None => Subst.set _ _ u1 e2 s
                  | Some e1' => exprUnify n s e1' e2
                end
              | _ , UVar u2 =>
                match Subst.lookup _ _ u2 s with
                  | None => Subst.set _ _ u2 e1 s
                  | Some e2' => exprUnify n s e1 e2'
                end
              | Var v1 , Var v2 =>
                if EqNat.beq_nat v1 v2 then Some s else None
              | Func f1 ts1 , Func f2 fs2 =>
                if EqNat.beq_nat f1 f2 then Some s else None
              | App e1 es1 , App e2 es2 =>
                match unify s e1 e2 with
                  | None => None
                  | Some s' =>
                    (fix unifyArgs (s : Subst) (es1 es2 : exprs ts) {struct es1} : option Subst :=
                      match es1 , es2 with
                        | nil , nil => Some s
                        | e1 :: es1 , e2 :: es2 =>
                          match unify s e1 e2 with
                            | None => None
                            | Some s' => unifyArgs s' es1 es2
                          end
                        | _ , _ => None
                      end) s es1 es2
                end
              | Abs t1 e1 , Abs t2 e2 =>
                (* t1 = t2 since both terms have the same type *)
                (** TODO: I have to handle the change in binding structure.
                 ** For example,
                 ** (fun x => x) ~ (fun x => ?1) doesn't work
                 ** because the ?1 isn't going to have x in scope
                 **)
                unify s e1 e2
              | _ , _ => None
            end)
      end) 10).
  Defined.

End typed.
*)
