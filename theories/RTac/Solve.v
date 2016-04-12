Require Import ExtLib.Tactics.
Require Import MirrorCore.RTac.Core.
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

  Definition SOLVE (tac : rtac typ expr) : rtac typ expr :=
    fun tus tvs nus nvs ctx s g =>
      match is_solved (tac tus tvs nus nvs ctx s g) with
      | Some s => Solved s
      | _ => Fail
      end.

  Theorem SOLVE_sound
  : forall tac, rtac_sound tac -> rtac_sound (SOLVE tac).
  Proof.
    unfold SOLVE, rtac_sound.
    intros.
    specialize (H ctx s g).
    destruct (is_solved (tac (getUVars ctx) (getVars ctx) (length (getUVars ctx))
              (length (getVars ctx)) ctx s g)) eqn:?; subst; try apply rtac_spec_Fail.
    eapply is_solved_sound in Heqo.
    eapply Proper_rtac_spec_impl.
    { reflexivity. }
    { eapply Heqo. }
    { eapply H. reflexivity. }
  Qed.

  Fixpoint SOLVES (tacs : list (rtac typ expr)) : rtac typ expr :=
    match tacs with
    | nil => fun tus tvs nus nvs ctx s g => Fail
    | tac :: tacs =>
      let rec := SOLVES tacs in
      fun tus tvs nus nvs ctx s g =>
        match is_solved (tac tus tvs nus nvs ctx s g) with
        | Some s => Solved s
        | _ => rec tus tvs nus nvs ctx s g
        end
    end.

  Theorem SOLVES_sound
  : forall tacs, Forall rtac_sound tacs -> rtac_sound (SOLVES tacs).
  Proof.
    induction 1; simpl.
    { red. intros; subst. eapply rtac_spec_Fail. }
    { red.
      intros.
      destruct (is_solved (x (getUVars ctx) (getVars ctx) (length (getUVars ctx))
                             (length (getVars ctx)) ctx s g)) eqn:?; subst; eauto.
      eapply is_solved_sound in Heqo.
      eapply Proper_rtac_spec_impl.
      { reflexivity. }
      { eapply Heqo. }
      { eapply H. reflexivity. } }
  Qed.

End parameterized.

Arguments SOLVE {_ _} _%rtac _ _ _ _ _ _ _.
Arguments SOLVES {_ _} _%or_rtac _ _ _ _ _ _ _.