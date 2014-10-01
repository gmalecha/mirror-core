Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.RTac.Core.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Context {typ : Type}.
  Context {expr : Type}.
  Context {subst : Type}.
  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Subst_subst : Subst subst expr}.
  Context {SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst}.

  Fixpoint FIRST (tacs : list (rtac typ expr subst))
  : rtac typ expr subst :=
    fun ctx s gl =>
      match tacs with
        | nil => Fail
        | tac :: tacs' =>
          match tac ctx s gl with
            | Fail => FIRST tacs' ctx s gl
            | x => x
          end
      end.

  Theorem FIRST_sound
  : forall tus tvs tacs, Forall (rtac_sound tus tvs) tacs -> rtac_sound tus tvs (FIRST tacs).
  Proof.
    unfold FIRST.
    induction 1.
    { unfold rtac_sound.
      intros; subst. trivial. }
    { red; simpl; intros.
      subst.
      specialize (H ctx s g _ eq_refl).
      destruct (x ctx s g); auto.
      eapply IHForall. reflexivity. }
  Qed.

End parameterized.
