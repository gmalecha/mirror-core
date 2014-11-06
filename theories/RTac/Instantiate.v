Require Import ExtLib.Data.Sum.
Require Import ExtLib.Tactics.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.Simplify.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Context {typ : Type}.
  Context {expr : Type}.
  Context {subst : Type}.
  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Subst_subst : Subst subst expr}.
  Context {SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst}.

  Variable instantiate : (nat -> option expr) -> nat -> expr -> expr.

  Section instantiate.
    Definition INSTANTIATE
    : rtac typ expr subst :=
      @SIMPLIFY typ expr subst _
                (fun subst Subst_subst _ctx sub =>
                   instantiate (fun u => subst_lookup u sub) 0).
  End instantiate.

  Theorem INSTANTIATE_sound
  : forall tus tvs, rtac_sound tus tvs INSTANTIATE.
  Proof.
    intros. eapply SIMPLIFY_sound.
  Admitted.

End parameterized.
