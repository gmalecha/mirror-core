Require Import ExtLib.Data.Sum.
Require Import ExtLib.Tactics.
Require Import MirrorCore.InstantiateI.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.Simplify.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Context {typ : Type}.
  Context {expr : Type}.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {ExprUVar_expr : ExprUVar expr}.
  Context {ExprUVarOk_expr : ExprUVarOk ExprUVar_expr}.

  Definition INSTANTIATE
  : rtac typ expr :=
    @SIMPLIFY typ expr
              (fun subst Subst_subst _ctx sub =>
                 instantiate (fun u => subst_lookup u sub) 0).

  Theorem INSTANTIATE_sound : rtac_sound INSTANTIATE.
  Proof.
    intros. eapply SIMPLIFY_sound.
    intros; forward.
    unfold propD, exprD'_typ0 in *.
    forward.
    eapply (@instantiate_sound_ho  _ _ _ _ _ _ _ _ _ _ nil) in H3;
      [ | | eapply sem_preserves_if_ho_ctx_lookup; eauto ]; eauto.
    forward_reason; inv_all; subst.
    change_rewrite H3.
    intros.
    gather_facts.
    eapply Pure_pctxD; eauto.
    clear. firstorder. specialize (H HList.Hnil).
    revert H1. autorewrite with eq_rw.
    simpl in *. rewrite H.
    exact (fun x => x).
    constructor.
    { intros. eapply Pure_pctxD; eauto. }
    { intros.
      specialize (H6 us vs).
      eapply Ap_pctxD; eauto. }
  Qed.

End parameterized.
