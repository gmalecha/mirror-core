Require Import ExtLib.Tactics.
Require Import MirrorCore.RTac.CoreK.
Require Import MirrorCore.RTac.IsSolved.

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

  Definition SOLVEK (tac : rtacK typ expr) : rtacK typ expr :=
    fun ctx s g =>
      match is_solved (tac ctx s g) with
      | Some s => Solved s
      | _ => Fail
      end.

  Theorem SOLVEK_sound
  : forall tac, rtacK_sound tac -> rtacK_sound (SOLVEK tac).
  Proof.
    unfold SOLVEK, rtacK_sound.
    intros.
    specialize (H ctx s g).
    destruct (is_solved (tac ctx s g)) eqn:?; subst; try apply rtac_spec_Fail.
    eapply is_solved_sound in Heqo.
    eapply Proper_rtac_spec_impl.
    { reflexivity. }
    { eapply Heqo. }
    { eapply H. reflexivity. }
  Qed.

  Theorem WF_SOLVEK : forall tac, WellFormed_rtacK tac -> WellFormed_rtacK (SOLVEK tac).
  Proof.
    unfold SOLVEK, WellFormed_rtacK. intros.
    subst. unfold rtacK_spec_wf in *.
    specialize (H ctx s g _ eq_refl).
    destruct (tac ctx s g); simpl; auto.
    destruct (is_solved_goal g0); auto.
    tauto.
  Qed.

  Fixpoint SOLVESK (tacs : list (rtacK typ expr)) : rtacK typ expr :=
    match tacs with
    | nil => fun ctx s g => Fail
    | tac :: tacs =>
      let rec := SOLVESK tacs in
      fun ctx s g =>
        match is_solved (tac ctx s g) with
        | Some s => Solved s
        | _ => rec ctx s g
        end
    end.

  Theorem SOLVES_sound
  : forall tacs, Forall rtacK_sound tacs -> rtacK_sound (SOLVESK tacs).
  Proof.
    induction 1; simpl.
    { red. intros; subst. eapply rtac_spec_Fail. }
    { red.
      intros.
      destruct (is_solved (x ctx s g)) eqn:?; subst; eauto.
      eapply is_solved_sound in Heqo.
      eapply Proper_rtac_spec_impl.
      { reflexivity. }
      { eapply Heqo. }
      { eapply H. reflexivity. } }
  Qed.

End parameterized.

Typeclasses Opaque SOLVEK SOLVESK.
Hint Opaque SOLVEK SOLVESK : typeclass_instances.

Arguments SOLVEK {_ _} _%rtac _ _ _.
Arguments SOLVESK {_ _} _%or_rtac _ _ _.