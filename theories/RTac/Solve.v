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

  Fixpoint SOLVES (tacs : list (rtac typ expr)) : rtac typ expr :=
    match tacs with
    | nil => fun tus tvs nus nvs ctx s g => Fail
    | tac :: tacs =>
      let rec := SOLVES tacs in
      fun tus tvs nus nvs ctx s g =>
        match tac tus tvs nus nvs ctx s g with
        | Solved s => Solved s
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
      specialize (H ctx s g _ eq_refl).
      destruct (x (getUVars ctx) (getVars ctx)
                  (length (getUVars ctx)) (length (getVars ctx)) ctx s g); auto.
      subst; auto. }
  Qed.

End parameterized.

Arguments SOLVE {_ _} _%rtac _ _ _ _ _ _ _.
Arguments SOLVES {_ _} _%or_rtac _ _ _ _ _ _ _.