Require Import ExtLib.Tactics.
Require Import MirrorCore.RTac.Core.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Context {typ : Type}.
  Context {expr : Type}.
  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {ExprUVar_expr : ExprUVar expr}.

  Definition SOLVE (tac : rtac typ expr) : rtac typ expr :=
    fun tus tvs nus nvs ctx s g =>
      match tac tus tvs nus nvs ctx s g with
        | Solved s => Solved s
        | _ => Fail
      end.

  Theorem SOLVE_sound
  : forall tac, rtac_sound tac -> rtac_sound (SOLVE tac).
  Proof.
    unfold SOLVE, rtac_sound.
    intros.
    specialize (H ctx s g).
    subst; destruct (tac (getUVars ctx) (getVars ctx)
           (length (getUVars ctx)) (length (getVars ctx)) ctx s g); auto.
    specialize (H _ eq_refl).
    eapply rtac_spec_Fail.
  Qed.

End parameterized.
