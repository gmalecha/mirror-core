Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.ExprDAs.
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

  Definition THEN (c1 c2 : rtac typ expr subst) : rtac typ expr subst :=
    fun gl =>
      match c1 gl with
        | Some gl' => c2 gl'
        | None => None
      end.

  Theorem THEN_sound
  : forall (tus tvs : list typ) (tac1 tac2 : rtac typ expr subst),
      rtac_sound tus tvs tac1 ->
      rtac_sound tus tvs tac2 ->
      rtac_sound tus tvs (THEN tac1 tac2).
  Proof.
    unfold THEN.
    intros.
    red. intros.
    forward.
    eapply H in H1; clear H.
    eapply H1 in H2; clear H1.
    destruct H2.
    eapply H0 in H3; eauto.
    specialize (H3 H). forward_reason.
    split; auto.
    forward. eauto.
  Qed.

End parameterized.