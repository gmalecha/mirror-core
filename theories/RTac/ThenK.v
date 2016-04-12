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
  Context {Expr_expr : Expr typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {ExprUVar_expr : ExprUVar expr}.

  Definition THENK (c1 : rtacK typ expr)
             (c2 : rtacK typ expr)
  : rtacK typ expr :=
    fun tus tvs nus nvs ctx sub g =>
      match c1 tus tvs nus nvs ctx sub g with
        | More_ sub' g' => c2 tus tvs nus nvs _ sub' g'
        | Solved sub => Solved sub
        | Fail => Fail
      end.

  Theorem THENK_sound
  : forall (tac1 : rtacK typ expr) (tac2 : rtacK typ expr),
      rtacK_sound tac1 ->
      rtacK_sound tac2 ->
      rtacK_sound (THENK tac1 tac2).
  Proof.
    unfold THENK.
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

Hint Opaque THENK : typeclass_instances.

Arguments THENK {typ expr} _%rtacK _%rtacK _ _ _ _ {_} _ _ : rename.

Notation "X  ;;; Y" := (@THENK _ _ X%rtacK Y%rtacK) (at level 70, right associativity) : rtacK_scope.
Require Import MirrorCore.RTac.RunOnGoals.
Notation "X  ;; Y" := (@THENK _ _ (runOnGoals X%rtac) Y%rtacK) (at level 70, right associativity) : rtacK_scope.
