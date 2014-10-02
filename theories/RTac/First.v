Require Import ExtLib.Tactics.
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
    fun ctx s gl =>
      match tacs with
        | nil => Fail
        | tac :: tacs' =>
          match tac ctx s gl with
            | Fail => FIRST tacs' ctx s gl
            | x => x
          end
      end.

(*
  Theorem FIRST_sound
  : forall tus tvs tacs, Forall (rtac_sound tus tvs) tacs -> rtac_sound tus tvs (FIRST tacs).
  Proof.
    unfold FIRST.
    induction 1.
    { unfold rtac_sound. intros; congruence. }
    { admit. }
  Qed.
*)

End parameterized.
