Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.CtxLogic.

Set Implicit Arguments.
Set Strict Implicit.

Section instantiate.
  Variable typ : Type.
  Variable expr : Type.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Expr_expr : @Expr typ _ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.

  Definition instantiate (f : uvar -> option expr) (n : nat) (e : expr) : expr :=
    expr_subst f (fun _ => None) n e.

  Definition sem_preserves_if_ho tus tvs
             (P : exprT tus tvs Prop -> Prop)
             (f : uvar -> option expr) : Prop :=
    forall u e t get,
      f u = Some e ->
      nth_error_get_hlist_nth _ tus u = Some (@existT _ _ t get) ->
      exists eD,
        exprD' tus tvs e t = Some eD /\
        P (fun us vs => get us = eD us vs).

  Definition sem_preserves_if tus tvs
             (P : exprT tus tvs Prop)
             (f : uvar -> option expr) : Prop :=
    @sem_preserves_if_ho tus tvs
                         (fun P' => forall us vs, P us vs -> P' us vs) f.

  Definition instantiate_spec_ho
             (instantiate : (uvar -> option expr) -> nat -> expr -> expr)
    : Prop :=
    forall tus tvs f e tvs' t eD P (EApp : CtxLogic.ExprTApplicative P),
      sem_preserves_if_ho P f ->
      exprD' tus (tvs' ++ tvs) e t = Some eD ->
      exists eD',
        exprD' tus (tvs' ++ tvs) (instantiate f (length tvs') e) t = Some eD' /\
        P (fun us vs => forall vs',
               eD us (hlist_app vs' vs) = eD' us (hlist_app vs' vs)).

  Definition instantiate_spec
             (instantiate : (uvar -> option expr) -> nat -> expr -> expr)
  : Prop :=
    forall tus tvs f e tvs' t eD P,
      @sem_preserves_if tus tvs P f ->
      exprD' tus (tvs' ++ tvs) e t = Some eD ->
      exists eD',
        exprD' tus (tvs' ++ tvs) (instantiate f (length tvs') e) t = Some eD' /\
        forall us vs vs',
          P us vs ->
          eD us (hlist_app vs' vs) = eD' us (hlist_app vs' vs).

  Theorem instantiate_sound_ho
  : instantiate_spec_ho instantiate.
  Proof.
    red. unfold instantiate.
    intros. remember (expr_subst f (fun _ : var => None) (length tvs') e).
    symmetry in Heqy.
    eapply expr_subst_sound_ho
      with (tus:=tus) (tvs:=tvs) (tus':=tus) (tvs':=tvs) (_tvs:=tvs') (t:=t)
           (P:=fun Q => P (fun a b => Q a b a b)) (eD := eD) in Heqy;
      eauto.
    { clear - EApp.
      constructor.
      { intros. eapply exprTPure. eauto. }
      { intros. revert H0. eapply exprTAp. eauto. } }
    { clear Heqy H0. intros.
      specialize (H u).
      destruct (f u).
      { specialize (H _ _ _ eq_refl H1).
        forward_reason.
        eexists; split; eauto. }
      { eexists; split; eauto.
        eapply exprTPure; eauto. } }
    { intros; eexists; split; eauto.
      eapply exprTPure; eauto. }
  Qed.

  Theorem instantiate_sound
  : instantiate_spec instantiate.
  Proof.
    red. intros.
    eapply instantiate_sound_ho in H0; eauto.
    { forward_reason.
      eexists; split; eauto. }
    { eapply ExprTApplicative_foralls_impl. }
  Qed.

  Definition mentionsU_instantiate_spec
             (instantiate : (uvar -> option expr) -> nat -> expr -> expr)
             (mentionsU : uvar -> expr -> bool)
  : Prop :=
    forall f n e u,
      mentionsU u (instantiate f n e) = true <-> (** do i need iff? **)
      (   (f u = None /\ mentionsU u e = true)
       \/ exists u' e',
            f u' = Some e' /\
            mentionsU u' e = true /\
            mentionsU u e' = true).

  Theorem mentionsU_instantiate
  : mentionsU_instantiate_spec instantiate (@mentionsU _ _ _ _).
  Proof.
    red. intros.
    unfold instantiate.
    rewrite mentionsU_subst; eauto.
    split; destruct 1.
    { left. tauto. }
    { destruct H.
      { right. forward_reason. do 2 eexists; split; eauto. }
      { forward_reason. congruence. } }
    { left. tauto. }
    { forward_reason. right. left.
      do 2 eexists; split; eauto. }
  Qed.

  Corollary mentionsU_instantiate_false
  : forall uv f n e,
      mentionsU uv (instantiate f n e) = false <->
      (f uv = None -> mentionsU uv e = false) /\
      (forall u e',
         f u = Some e' ->
         mentionsU u e = true ->
         mentionsU uv e' = false).
  Proof.
    split; intros.
    { destruct (mentionsU_instantiate f n e uv).
      split. consider (mentionsU uv e); auto.
      { intros. exfalso.
        rewrite H2 in H. congruence.
        left; auto. }
      { intros.
        consider (mentionsU uv e'); auto; intro.
        rewrite H1 in H. congruence.
        clear H0.
        right. exists u. exists e'.
        split; auto. } }
    { consider (mentionsU uv (instantiate f n e)); auto.
      intros.
      eapply mentionsU_instantiate in H0.
      forward_reason.
      destruct H0.
      { destruct H0. apply H in H0. congruence. }
      { forward_reason.
        eapply H1 in H0; eauto. } }
  Qed.

  Theorem mentionsV_instantiate
  : forall v f n e,
      mentionsV v (instantiate f n e) = true <->
      (   mentionsV v e = true
       \/ (v >= n /\
           exists u e', mentionsU u e = true /\
                        f u = Some e' /\
                        mentionsV (v-n) e' = true)).
  Proof.
    red. intros.
    unfold instantiate.
    rewrite mentionsV_subst; eauto.
    split; destruct 1.
    { left. tauto. }
    { destruct H. destruct H0.
      { left; tauto. }
      destruct H0.
      { right. split; auto. }
      { forward_reason. congruence. } }
    { consider (v ?[ lt ] n); intros.
      { left. tauto. }
      { right. split. omega. left. tauto. } }
    { forward_reason. right. split; auto.
      right. left. eauto. }
  Qed.

  Theorem mentionsV_instantiate_0
  : forall v f e,
      mentionsV v (instantiate f 0 e) = true <->
      (   mentionsV v e = true
       \/ exists u e', mentionsU u e = true /\
                       f u = Some e' /\
                       mentionsV v e' = true).
  Proof.
    intros. rewrite mentionsV_instantiate.
    split; destruct 1; eauto.
    { right. rewrite <- Minus.minus_n_O in *. tauto. }
    { rewrite <- Minus.minus_n_O in *. right; split; try tauto. omega. }
  Qed.

  Theorem instantiate_noop
  : forall f n e,
      (forall u, mentionsU u e = true -> f u = None) ->
      instantiate f n e = e.
  Proof.
    intros. unfold instantiate.
    eapply expr_subst_noop; eauto.
  Qed.

  Theorem Proper_instantiate
  : Proper ((eq ==> eq) ==> eq ==> eq ==> eq)%signature instantiate.
  Proof.
    intros.
    red. red. red. red. unfold instantiate. intros; subst.
    eapply Proper_subst; eauto.
    red. auto.
  Qed.

End instantiate.

Arguments mentionsU_instantiate {typ expr RType RTypeOk Expr ExprOk} _ _ _ _ : rename.
Arguments mentionsU_instantiate_false {typ expr RType RTypeOk Expr ExprOk} _ _ _ _ : rename.