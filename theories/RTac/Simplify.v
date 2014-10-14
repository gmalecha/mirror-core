Require Import ExtLib.Data.Sum.
Require Import ExtLib.Tactics.
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

  Variable simplify : forall subst : Type,
                        Subst subst expr ->
                        Ctx typ expr -> subst -> expr -> expr.

  Fixpoint ctx_domain ctx (s : @ctx_subst typ expr subst ctx) : list nat :=
    match s with
      | TopSubst s => domain s
      | AllSubst _ _ cs' => ctx_domain cs'
      | HypSubst _ _ cs' => ctx_domain cs'
      | ExsSubst _ _ cs' s' => ctx_domain cs' ++ domain s'
    end.

  Instance Subst_ctx_subst ctx : Subst (@ctx_subst typ expr subst ctx) expr :=
  { lookup := @ctx_lookup _ _ _ _ ctx
  ; domain := @ctx_domain ctx }.

  Definition SIMPLIFY : rtac typ expr subst :=
    fun _ _ _ _ ctx sub gl =>
      More_ sub (GGoal (@simplify (ctx_subst subst ctx) _ ctx sub gl)).

  Hypothesis simplify_sound : False.

  Theorem SIMPLIFY_sound
  : forall tus tvs, rtac_sound tus tvs SIMPLIFY.
  Proof.
  Admitted.

End parameterized.
