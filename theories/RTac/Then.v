Require Import ExtLib.Tactics.
Require Import MirrorCore.RTac.Core.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Subst_subst : Subst subst expr}.
  Context {SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst}.
  Context {SubstUpdate_subst : SubstUpdate subst expr}.

  (** c2 is put closer to the goal **)
  Fixpoint Ctx_append (c1 c2 : Ctx typ expr) {struct c2} : Ctx typ expr :=
    match c2 with
      | CTop => c1
      | CAll c2' t => CAll (Ctx_append c1 c2') t
      | CEx  c2' t => CEx  (Ctx_append c1 c2') t
      | CHyp c2' h => CHyp (Ctx_append c1 c2') h
    end.

  Definition THEN (c1 c2 : rtac typ expr subst) : rtac typ expr subst :=
    fun ctx sub g =>
      match c1 ctx sub g with
        | More sub' g' =>
          runRTac c2 ctx sub' g'
        | Solved sub =>
          Solved sub
        | Fail => Fail
      end.

(*
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
*)
End parameterized.