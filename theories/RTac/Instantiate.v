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
  : @exprD'_instantiate _ _ _ _ instantiate.

  Definition INSTANTIATE
  : rtac typ expr :=
    @SIMPLIFY typ expr
              (fun subst Subst_subst _ctx sub =>
                 instantiate (fun u => subst_lookup u sub) 0).

  Theorem INSTANTIATE_sound : rtac_sound INSTANTIATE.
  Proof.
    intros. eapply SIMPLIFY_sound.
    intros; forward.
    (** TODO: This needs higher-order instantiation *)
  Admitted.

End parameterized.
