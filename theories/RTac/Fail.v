Require Import ExtLib.Tactics.
Require Import MirrorCore.RTac.Core.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Context {typ : Type}.
  Context {expr : Type}.

  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {ExprUVar_expr : ExprUVar expr}.

  Definition FAIL : rtac typ expr :=
    fun _ _ _ _ _ _ _ => Fail.

  Theorem FAIL_sound
  : rtac_sound FAIL.
  Proof.
    unfold FAIL, rtac_sound.
    intros; subst.
    eapply rtac_spec_Fail.
  Qed.

End parameterized.
