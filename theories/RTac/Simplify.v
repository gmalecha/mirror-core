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

(*
  Hypothesis simplify_sound
  : forall subst Subst_subst tus tvs ctx s e e',
      @simplify subst Subst_subst ctx s e = e' ->
      match pctxD tus tvs ctx
          , substD (tus ++ getUVars ctx) (tvs ++ getVars ctx) s
          , propD (tus ++ getUVars ctx) (tvs ++ getVars ctx) e
          , propD (tus ++ getUVars ctx) (tvs ++ getVars ctx) e'
      with
        | None , _ , _ , _ => True
        | _ , None , _ , _ => True
        | _ , _ , None , _ => True
        | _ , _ , _ , None => False
        | Some cD , Some sD , Some eD , Some eD' =>
          forall us vs,
            cD (fun us vs => sD us vs -> (eD us vs <-> eD' us vs)) us vs
      end.
*)

  Theorem SIMPLIFY_sound
  : forall tus tvs, rtac_sound tus tvs SIMPLIFY.
  Proof.
    red; intros; subst.
    simpl. intros; split; eauto.
    forward.
  Admitted.

End parameterized.
