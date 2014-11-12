Require Import ExtLib.Tactics.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.CoreK.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Context {typ : Type}.
  Context {expr : Type}.

  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {ExprUVar_expr : ExprUVar expr}.

  Definition THEN (c1 : rtac typ expr)
             (c2 : rtacK typ expr)
  : rtac typ expr :=
    fun tus tvs nus nvs ctx sub g =>
      match c1 tus tvs nus nvs ctx sub g with
        | More_ sub' g' => c2 tus tvs nus nvs _ sub' g'
        | Solved sub => Solved sub
        | Fail => Fail
      end.

  Theorem THEN_sound
  : forall (tac1 : rtac typ expr) (tac2 : rtacK typ expr),
      rtac_sound tac1 ->
      rtacK_sound tac2 ->
      rtac_sound (THEN tac1 tac2).
  Proof.
    unfold THEN.
    intros.
    red. intros. subst.
    specialize (H ctx s g _ eq_refl).
    match goal with
      | |- context [ match ?X with _ => _ end ] =>
        destruct X; auto
    end.
    eapply rtac_spec_trans; eauto.
    eapply H0. reflexivity.
  Qed.

End parameterized.