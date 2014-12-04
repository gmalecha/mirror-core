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
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {ExprUVar_expr : ExprUVar expr}.

  Fixpoint FIRST (tacs : list (rtac typ expr))
  : rtac typ expr :=
    fun tus tvs nus nvs ctx s gl =>
      match tacs with
        | nil => Fail
        | tac :: tacs' =>
          match tac tus tvs nus nvs ctx s gl with
            | Fail => @FIRST tacs' tus tvs nus nvs ctx s gl
            | x => x
          end
      end.

  Theorem FIRST_sound
  : forall tacs, Forall (rtac_sound) tacs -> rtac_sound (FIRST tacs).
  Proof.
    unfold FIRST.
    induction 1.
    { unfold rtac_sound. intros; subst; simpl; auto. }
    { red. intros.
      specialize (H ctx s g _ eq_refl).
      subst. destruct (x (getUVars ctx) (getVars ctx)
         (length (getUVars ctx)) (length (getVars ctx)) ctx s g); eauto. }
  Qed.

  Fixpoint FIRSTK (tacs : list (rtacK typ expr))
  : rtacK typ expr :=
    fun tus tvs nus nvs ctx s gl =>
      match tacs with
        | nil => Fail
        | tac :: tacs' =>
          match tac tus tvs nus nvs ctx s gl with
            | Fail => @FIRSTK tacs' tus tvs nus nvs ctx s gl
            | x => x
          end
      end.

  Theorem FIRSTK_sound
  : forall tacs, Forall (rtacK_sound) tacs -> rtacK_sound (FIRSTK tacs).
  Proof.
    unfold FIRSTK.
    induction 1.
    { unfold rtacK_sound. intros; subst; simpl; auto. }
    { red. intros.
      specialize (H ctx s g _ eq_refl).
      subst. destruct (x (getUVars ctx) (getVars ctx)
         (length (getUVars ctx)) (length (getVars ctx)) ctx s g); eauto. }
  Qed.

End parameterized.
