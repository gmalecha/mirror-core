Require Import ExtLib.Tactics.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.RunOnGoals.

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

  Definition THEN (c1 c2 : rtac typ expr subst) : rtac typ expr subst :=
    fun tus tvs nus nvs ctx sub g =>
      match c1 tus tvs nus nvs ctx sub g with
        | More_ sub' g' => runOnGoals c2 tus tvs nus nvs _ sub' g'
        | Solved sub => Solved sub
        | Fail => Fail
      end.

  Theorem THEN_sound
  : forall (tus tvs : list typ) (tac1 tac2 : rtac typ expr subst),
      rtac_sound tus tvs tac1 ->
      rtac_sound tus tvs tac2 ->
      rtac_sound tus tvs (THEN tac1 tac2).
  Proof.
    unfold THEN.
    intros.
    red. intros. subst.
    specialize (H ctx s g _ eq_refl).
    match goal with
      | |- context [ match ?X with _ => _ end ] =>
        destruct X; auto
    end.
    eapply rtac_spec_trans; eauto.
    eapply runOnGoals_sound with (ctx := ctx) (s := c) (g := g0) in H0.
    rewrite countUVars_getUVars in H0.
    rewrite countVars_getVars in H0.
    do 2 rewrite <- app_length in H0.
    eauto.
  Qed.

End parameterized.