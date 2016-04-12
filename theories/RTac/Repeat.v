Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.List.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.RunOnGoals.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Context {typ expr : Type}.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Expr_expr : Expr typ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {ExprUVar_expr : ExprUVar expr}.
  Context {ExprUVarOk_expr : ExprUVarOk _}.

  (** TODO: Write this with a positive **)
  Section repeater.
    (** TODO: To be efficient, this should be written in CPS
     **)
    Variable tac : rtac typ expr.

    Fixpoint REPEAT' (n : nat) {struct n}
    : rtac typ expr :=
      fun tus tvs nus nvs ctx sub gl =>
        match n with
          | 0 => More_ sub (GGoal gl)
          | S n =>
            match @tac tus tvs nus nvs ctx sub gl with
              | Fail => More_ sub (GGoal gl)
              | More_ sub' gl' =>
                runOnGoals (fun x => REPEAT' n x) tus tvs nus nvs sub' gl'
              | Solved s => Solved s
            end
        end.
  End repeater.

  Definition REPEAT n (tac : rtac typ expr)
  : rtac typ expr :=
    REPEAT' tac n.

  Theorem REPEAT_sound
  : forall n tac, rtac_sound tac ->
                  rtac_sound (REPEAT n tac).
  Proof.
    unfold REPEAT. intros n tac H.
    induction n.
    - simpl.
      red; intros; subst.
      eapply rtac_spec_More_; auto.
    - simpl. red; intros; subst.
      specialize (H ctx s g _ eq_refl).
      destruct (tac (getUVars ctx) (getVars ctx)
                    (length (getUVars ctx)) (length (getVars ctx))
                    ctx s g); auto using rtac_spec_More_.
      eapply rtac_spec_trans; eauto.
      eapply runOnGoals_sound in IHn.
      revert IHn.
      intro. eapply IHn.
      simpl. reflexivity.
  Qed.

End parameterized.

Hint Opaque REPEAT : typeclass_instances.
Typeclasses Opaque REPEAT.

Arguments REPEAT {_ _ _ _} _%nat _%rtac _ _ _ _ _ _ _.
