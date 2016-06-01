Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relations.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.Rewrite.Core.

Set Implicit Arguments.
Set Strict Implicit.

Set Suggest Proof Using.

Section setoid.
  Context {typ : Type}.
  Context {func : Type}.
  Context {RType_typD : RType typ}.
  Context {Typ2_Fun : Typ2 RType_typD RFun}.
  Context {RSym_func : RSym func}.

  (** Reasoning principles **)
  Context {RTypeOk_typD : RTypeOk}.
  Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.
  Context {RSymOk_func : RSymOk RSym_func}.
  Context {Typ0_Prop : Typ0 _ Prop}.

  (** TODO(gmalecha): This is not necessary *)
  Context {RelDec_eq_typ : RelDec (@eq typ)}.
  Context {RelDec_Correct_eq_typ : RelDec_Correct RelDec_eq_typ}.

  Local Existing Instance Subst_ctx_subst.
  Local Existing Instance SubstOk_ctx_subst.
  Local Existing Instance SubstUpdate_ctx_subst.
  Local Existing Instance SubstUpdateOk_ctx_subst.
  Local Existing Instance Expr_expr.
  Local Existing Instance ExprOk_expr.

  (* TODO(gmalecha): Wrap all of this up in a type class?
   * Why should it be different than Expr?
   *)
  Variable Rbase : Type.
  Variable Rbase_eq : Rbase -> Rbase -> bool.
  Hypothesis Rbase_eq_ok : forall a b, Rbase_eq a b = true -> a = b.

  Local Notation "'R'" := (R typ Rbase).

  Variable RbaseD : Rbase -> forall t : typ, option (typD t -> typD t -> Prop).

  Variable reducer : expr typ func -> expr typ func.
  Variable rwa : RwAction typ func Rbase.

  Definition rw_simplify : RwAction _ _ _ :=
    fun e => rwa (reducer e).

  Hypothesis reducer_sound
  : forall tus tvs t e eD,
      lambda_exprD tus tvs t e = Some eD ->
      exists eD',
        lambda_exprD tus tvs t (reducer e) = Some eD' /\
        forall us vs, eD us vs = eD' us vs.

  Hypothesis rwa_sound : setoid_rewrite_spec RbaseD rwa.

  Theorem rw_simplify_sound
  : setoid_rewrite_spec RbaseD rw_simplify.
  Proof using rwa_sound reducer_sound.
    unfold rw_simplify. do 2 red. intros.
    eapply rwa_sound in H; eauto.
    forward_reason; split; eauto.
    intros. eapply H1 in H2; clear H1.
    forward.
    specialize (@reducer_sound _ _ _ _ _ H3).
    destruct reducer_sound as [ ? [ ? ? ] ].
    rewrite H4 in *.
    destruct (pctxD cs') eqn:?; auto.
    destruct e'.
    { simpl in *.
      forward.
      destruct H6; split; auto.
      intros.
      gather_facts.
      eapply Pure_pctxD; eauto.
      intros. rewrite H5. eauto. }
    { simpl in *. rewrite H4 in *.
      rewrite H3.
      destruct H2; split; auto.
      intros.
      gather_facts.
      eapply Pure_pctxD; eauto.
      intros. rewrite H5.
      auto. }
  Qed.

  Definition rw_post_simplify : RwAction _ _ _ :=
    Eval unfold rw_bind, rw_ret in
      fun e r => rw_bind (rwa e r)
                         (fun e' => rw_ret match e' with
                                           | Progress e' => Progress (reducer e')
                                           | NoProgress => NoProgress
                                           end).

  Theorem rw_post_simplify_sound
  : setoid_rewrite_spec RbaseD rw_post_simplify.
  Proof using rwa_sound reducer_sound.
    unfold rw_post_simplify. do 2 red. intros.
    forward. inv_all; subst.
    eapply rwa_sound in H1; eauto.
    forward_reason; split; eauto.
    intros. eapply H1 in H2; clear H1.
    destruct (pctxD cs) eqn:?; auto.
    destruct (lambda_exprD (getUVars ctx) (tvs' ++ getVars ctx) t e) eqn:?; auto.
    destruct (pctxD cs') eqn:?; auto.
    destruct p0; simpl in *.
    { destruct (lambda_exprD (getUVars ctx) (tvs' ++ getVars ctx) t new_val) eqn:?; try contradiction.
      eapply reducer_sound in Heqo2.
      destruct Heqo2 as [ ? [ ? ? ] ].
      rewrite H1. destruct H2; split; auto.
      intros.
      gather_facts.
      eapply Pure_pctxD; eauto.
      intros. rewrite <- H3. eauto. }
    { destruct (lambda_exprD (getUVars ctx) (tvs' ++ getVars ctx) t e); auto. }
  Qed.

End setoid.
