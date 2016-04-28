(** The Rtac tactic that is used to invoke the rewriter
 **)
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.Compat.
Require Import MirrorCore.Util.Iteration.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.Rewrite.Core.
Require Import MirrorCore.Lambda.Rewrite.BottomUp.

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

  (* TODO(gmalecha): Wrap all of this up in a type class?
   * Why should it be different than Expr?
   *)
  Variable Rbase : Type.
  Variable Rbase_eq : Rbase -> Rbase -> bool.
  Hypothesis Rbase_eq_ok : forall a b, Rbase_eq a b = true -> a = b.

  Local Notation "'R'" := (R typ Rbase).

  Variable RbaseD : Rbase -> forall t : typ, option (typD t -> typD t -> Prop).

  Hypothesis RbaseD_single_type
  : forall r t1 t2 rD1 rD2,
      RbaseD r t1 = Some rD1 ->
      RbaseD r t2 = Some rD2 ->
      t1 = t2.

  Local Existing Instance Subst_ctx_subst.
  Local Existing Instance SubstOk_ctx_subst.
  Local Existing Instance SubstUpdate_ctx_subst.
  Local Existing Instance SubstUpdateOk_ctx_subst.
  Local Existing Instance Expr_expr.
  Local Existing Instance ExprOk_expr.

  Definition auto_setoid_rewrite_bu
             (r : R)
             (reflexive : refl_dec R)
             (transitive : trans_dec R)
             (rewriter : RwAction typ func Rbase)
             (respectful : ResolveProper typ func Rbase)
  : rtac typ (expr typ func) :=
    let rw := bottom_up reflexive transitive rewriter respectful in
    fun ctx cs g =>
      match @rw g r nil ctx cs with
      | None => Fail
      | Some (Progress g', cs') => More_ cs' (GGoal g')
      | Some (NoProgress, cs') => Fail
      end.

  Variable R_impl : R.

  Hypothesis R_impl_is_impl
    : RD RbaseD R_impl (typ0 (F:=Prop)) =
      Some match eq_sym (typ0_cast (F:=Prop)) in _ = t return t -> t -> Prop with
           | eq_refl => Basics.impl
           end.

  Theorem auto_setoid_rewrite_bu_sound
  : forall is_refl is_trans rw proper
           (His_reflOk : refl_dec_ok (RD RbaseD) is_refl)
           (His_transOk : trans_dec_ok (RD RbaseD) is_trans),
      setoid_rewrite_spec RbaseD rw ->
      respectful_spec RbaseD  proper ->
      rtac_sound (auto_setoid_rewrite_bu (Rflip R_impl)
                                         is_refl is_trans rw proper).
  Proof using RSymOk_func RTypeOk_typD R_impl_is_impl
        RbaseD_single_type Typ2Ok_Fun.
    intros. unfold auto_setoid_rewrite_bu. red.
    intros.
    generalize (@bottom_up_sound _ _ _ _ _ _ _ _ _ _ _
                                 RbaseD_single_type is_refl is_trans rw proper
                                 His_reflOk His_transOk H H0 g (Rflip R_impl) ctx s nil).
    simpl.
    destruct (bottom_up is_refl is_trans rw proper g (Rflip R_impl) nil s).
    { destruct p. destruct p; subst; eauto using rtac_spec_Fail.
      red. intros Hbus ? ?.
      specialize (Hbus _ _ eq_refl H2).
      forward_reason.
      split; try assumption.
      split; [ constructor | ].
      specialize (H4 (typ0 (F:=Prop))).
      rewrite R_impl_is_impl in H4.
      specialize (H4 _ eq_refl).
      revert H4.
      destruct (pctxD s) eqn:HpctxDs; try (clear; tauto).
      simpl. unfold propD. unfold exprD_typ0.
      simpl.
      destruct (lambda_exprD (getUVars ctx) (getVars ctx) (typ0 (F:=Prop)) g);
        try solve [ tauto ].
      destruct (pctxD c) eqn:HpctxDc; try solve [ tauto ].
      destruct (lambda_exprD (getUVars ctx) (getVars ctx) (typ0 (F:=Prop)) new_val);
        try solve [ tauto ].
      destruct 1; split; try assumption.
      intros.
      gather_facts.
      eapply Pure_pctxD; eauto.
      intros.
      specialize (H5 Hnil). simpl in *.
      revert H6 H5. autorewrite_with_eq_rw.
      clear. generalize (typ0_cast (F:=Prop)).
      generalize dependent (typD (typ0 (F:=Prop))).
      do 4 intro. subst. simpl.
      unfold flip, Basics.impl. tauto. }
    { subst. intro. clear.
      eapply rtac_spec_Fail. }
  Qed.

End setoid.
