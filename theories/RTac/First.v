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
  Context {SubstUpdate_subst : SubstUpdate subst expr}.
  Context {SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst}.

  Fixpoint FIRST (tacs : list (rtac typ expr subst))
  : rtac typ expr subst :=
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
  : forall tus tvs tacs, Forall (rtac_sound tus tvs) tacs -> rtac_sound tus tvs (FIRST tacs).
  Proof.
    unfold FIRST.
    induction 1.
    { unfold rtac_sound. intros; subst; simpl; auto. }
    { red. intros.
      specialize (H ctx s g _ eq_refl).
      subst. destruct (x (tus ++ getUVars ctx) (tvs ++ getVars ctx)
         (length (tus ++ getUVars ctx)) (length (tvs ++ getVars ctx)) ctx s g); eauto. }
  Qed.

End parameterized.
