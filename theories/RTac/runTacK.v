Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.CoreK.

Section runTacK.
  Context {typ expr : Set}.
  Variable RType_typ : RType typ.
  Variable Typ0_Prop : Typ0 RType_typ Prop.
  Variable Expr_expr : Expr typ expr.
  Variable ExprUVar_expr : ExprUVar expr.

  Definition runTacK (tac : rtacK typ expr) : rtac typ expr :=
    fun e f g => tac e f (GGoal g).

  Theorem runTacK_sound : forall t, rtacK_sound t -> rtac_sound (runTacK t).
  Proof.
    intro. unfold runTacK. simpl.
    unfold rtac_sound, rtacK_sound, rtac_spec, rtacK_spec.
    simpl. intros.
    specialize (H _ _ _ _ H0).
    subst. assumption.
  Qed.
End runTacK.
