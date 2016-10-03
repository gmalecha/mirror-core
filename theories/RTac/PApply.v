Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Tactics.

Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.Polymorphic.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.LemmaApply.
Require Import MirrorCore.UnifyI.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.Reduce.
Require Import MirrorCore.RTac.Apply.
Require Import MirrorCore.RTac.AtGoal.
Require Import MirrorCore.RTac.Fail.

Require Import MirrorCore.Lambda.PolyInst.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprVariables.

Require Import MirrorCore.MTypes.ModularTypes.
Require Import MirrorCore.MTypes.MTypeUnify.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
Check @get_inst.
  Context {tsym : nat -> Type} {func : Type}.
  Let typ := mtyp tsym.

  Context {RType_typ : RType typ}.
  Context {RSym_func : RSym func}.
  Context {Typ2_Fun : Typ2 RType_typ RFun}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Typ0_Prop : Typ0 _ Prop}.

  Context {RTypeOk_typD : RTypeOk}.
  Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.
  Context {RSymOk_func : RSymOk RSym_func}.

  Local Existing Instance Subst_ctx_subst.
  Local Existing Instance SubstOk_ctx_subst.
  Local Existing Instance SubstUpdate_ctx_subst.
  Local Existing Instance SubstUpdateOk_ctx_subst.
  Local Existing Instance Expr_expr.
  Local Existing Instance ExprOk_expr.
  Local Existing Instance ExprUVar_expr.
  Local Existing Instance ExprUVarOk_expr.

  Variable exprUnify : forall subst, Subst subst (expr typ func) -> SubstUpdate subst (expr typ func) ->
    unifier typ (expr typ func) subst.

  Variable exprUnify_sound
  : forall subst (S : Subst subst (expr typ func)) (SO : SubstOk subst typ (expr typ func)) SU (SUO : SubstUpdateOk subst typ (expr typ func)),
      unify_sound (@exprUnify subst S SU).

  Variable lem : Lemma.lemma typ (expr typ func) (expr typ func).

  Local Definition view_update :=
    (mtype_unify tsym).

  Local Definition get_lemma {n : nat}
        (plem : polymorphic typ n (Lemma.lemma typ (expr typ func) (expr typ func)))
(*        (tc : polymorphic typ n bool)*)
        (e : expr typ func)
  : option (lemma typ (expr typ func) (expr typ func)) :=
    match
      get_inst tyVar view_update (fmap (fun x => x.(concl)) plem) e
    with
    | None => None
    | Some args => Some (inst plem args)
(*      if (inst tc args)
      then Some (inst plem args)
      else None*)
    end.

  Definition PAPPLY {n : nat} 
             (plem : polymorphic typ n (Lemma.lemma typ (expr typ func) (expr typ func))) : 
    rtac typ (expr typ func) :=
    AT_GOAL (fun _ c gl =>
               match get_lemma plem gl with
               | None => FAIL
               | Some lem => APPLY exprUnify lem
               end).

(*
  Hypothesis lemD : ReifiedLemma lem.

  Theorem APPLY_sound : rtac_sound APPLY.
  Proof.
    eapply EAPPLY_sound; eauto.
  Qed.
*)
End parameterized.

Hint Opaque PAPPLY : typeclass_instances.

Arguments PAPPLY {typ expr _ _ _ _} unify {_} lem _ _ _ : rename.