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
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Variable RType_typ : RType typ.
  Variable Expr_expr : Expr RType_typ expr.
  Variable Typ0_Prop : Typ0 _ Prop.
  Variable Subst_subst : Subst subst expr.
  Variable SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst.

  Fixpoint FIRST (tacs : list (rtac typ expr subst))
  : rtac typ expr subst :=
    fun gl =>
      match tacs with
        | nil => None
        | tac :: tacs' =>
          match tac gl with
            | None => FIRST tacs' gl
            | Some gl' => Some gl'
          end
      end.

  Theorem FIRST_sound
  : forall tus tvs tacs, Forall (rtac_sound tus tvs) tacs -> rtac_sound tus tvs (FIRST tacs).
  Proof.
    unfold FIRST.
    induction 1.
    { unfold rtac_sound. intros; congruence. }
    { admit. }
  Qed.

End parameterized.
