Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.RTac.Core.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

(** TODO: Can I do alternation if I can do strengthening of both
 ** unification variables and regular variables?
 ** 1) This means that substD needs strengthening
 ** 2) It also means that hypotheses need to be eliminatable
 **
 **    goal :=
 **      Alls : list typ -> goal -> goal
 **    | Exs : list typ -> goal -> goal
 **    | Hyps : list expr -> goal -> goal
 **    | Goal : expr -> goal.
 **
 **)
Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Variable RType_typ : RType typ.
  Variable Expr_expr : Expr RType_typ expr.
  Variable Typ0_Prop : Typ0 _ Prop.
  Variable Subst_subst : Subst subst expr.
  Variable SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst.

  Definition TRY (tac : rtac typ expr subst) : rtac typ expr subst :=
    fun gl => match tac gl with
                | None => Some gl
                | Some gl' => Some gl'
              end.

  Theorem TRY_sound
  : forall tus tvs tac, rtac_sound tus tvs tac -> rtac_sound tus tvs (TRY tac).
  Proof.
    unfold TRY, rtac_sound.
    intros.
    specialize (H g g').
    destruct (tac g); inv_all; subst.
    { eapply H; eauto. }
    { forward. }
  Qed.

End parameterized.
