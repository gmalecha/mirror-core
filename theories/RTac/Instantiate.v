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

  Variable instantiate : (nat -> option expr) -> nat -> expr -> expr.
  Variable exprD'_instantiate
  : @sem_instantiate_ho _ _ _ _ _ _ iff (@propD _ _ _ _ _) instantiate.

  Definition INSTANTIATE
  : rtac typ expr :=
    @SIMPLIFY typ expr
              (fun subst Subst_subst _ctx sub =>
                 instantiate (fun u => subst_lookup u sub) 0).

  Theorem INSTANTIATE_sound : rtac_sound INSTANTIATE.
  Proof.
    intros. eapply SIMPLIFY_sound.
    intros; forward.
    red in exprD'_instantiate.
    eapply exprD'_instantiate with (tvs' := nil) in H3;
      [ | | eapply sem_preserves_if_ho_ctx_lookup; eauto ].
    { subst. forward_reason.
      change_rewrite H.
      intros.
      gather_facts.
      eapply Pure_pctxD; eauto.
      clear. firstorder. specialize (H HList.Hnil). simpl in *.
      destruct H. assumption. }
    { clear - H1. constructor; eauto.
      - intros. eapply Pure_pctxD; eauto.
      - intros. gather_facts.
        eapply Pure_pctxD; eauto. }
  Qed.

End parameterized.
