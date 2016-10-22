Require Import ExtLib.Tactics.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.CoreK.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Context {typ : Set}.
  Context {expr : Set}.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Expr_expr : Expr typ expr}.
  Context {ExprUVar_expr : ExprUVar expr}.

  Fixpoint FIRST (tacs : list (rtac typ expr))
  : rtac typ expr :=
    fun ctx s gl =>
      match tacs with
      | nil => Fail
      | tac :: tacs' =>
        match tac ctx s gl with
        | Fail => @FIRST tacs' ctx s gl
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
      subst. destruct (x ctx s g); eauto. }
  Qed.

  Fixpoint FIRSTK (tacs : list (rtacK typ expr))
  : rtacK typ expr :=
    fun ctx s gl =>
      match tacs with
        | nil => Fail
        | tac :: tacs' =>
          match tac ctx s gl with
            | Fail => @FIRSTK tacs' ctx s gl
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
      subst. destruct (x ctx s g); eauto. }
  Qed.

End parameterized.

Hint Opaque FIRST FIRSTK : typeclass_instances.

Arguments FIRST {typ expr} _%or_rtac _ _ _ : rename.
Arguments FIRSTK {typ expr} _%or_rtacK _ _ _ : rename.

Section parse_demo.
  Variable IDTAC : rtac unit unit.
  Variable IDTACK : rtacK unit unit.

  Goal @eq (rtac unit unit) (FIRST nil) (FIRST [ ])%rtac.
    reflexivity.
  Abort.
  Goal @eq (rtac unit unit) (FIRST (IDTAC :: nil)) (FIRST [ IDTAC ])%rtac.
    reflexivity.
  Abort.
  Goal @eq (rtac unit unit) (FIRST (IDTAC :: FIRST (IDTAC :: nil) :: IDTAC :: nil))
       (FIRST [ IDTAC | FIRST [ IDTAC ] | IDTAC ])%rtac.
    reflexivity.
  Abort.

  Goal @eq (rtacK unit unit) (FIRSTK nil) (FIRSTK [ ])%rtac.
    reflexivity.
  Abort.
  Goal @eq (rtacK unit unit) (FIRSTK (IDTACK :: nil)) (FIRSTK [ IDTACK ])%rtac.
    reflexivity.
  Abort.
  Goal @eq (rtacK unit unit) (FIRSTK (IDTACK :: FIRSTK (IDTACK :: nil) :: IDTACK :: nil))
       (FIRSTK [ IDTACK | FIRSTK [ IDTACK ] | IDTACK ])%rtac.
    reflexivity.
  Abort.
End parse_demo.
