Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Tactics.

Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.Polymorphic.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.PLemma.
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

Require Import MirrorCore.CTypes.CoreTypes.
Require Import MirrorCore.CTypes.CTypeUnify.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Context {tsym : nat -> Set} {func : Set}.
  Let typ := ctyp tsym.

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
    (ctype_unify tsym).

  Local Definition get_lemma su
        (plem : PolyLemma typ (expr typ func) (expr typ func))
        (e : expr typ func)
  : option (lemma typ (expr typ func) (expr typ func)) :=
    match
      get_inst tyVar su (fmap (fun x => x.(concl)) (p_lem plem)) e
    with
    | None => None
    | Some args =>
      if (inst (p_tc plem) args)
      then Some (inst (p_lem plem) args)
      else None
    end.

  Definition PAPPLY
             su
             (plem : PolyLemma typ (expr typ func) (expr typ func)) :
    rtac typ (expr typ func) :=
    AT_GOAL (fun _ c gl =>
               match get_lemma su plem gl with
               | None => FAIL
               | Some lem => APPLY exprUnify lem
               end).

  Class ReifiedPLemma (L : PolyLemma typ (expr typ func) (expr typ func)) : Prop := mkRPL
  { ReifiedPLemma_proof : PolyLemmaD (@exprD_typ0 _ _ _ _ Prop _) L }.


  Variable plem : PolyLemma typ (expr typ func) (expr typ func).
  Hypothesis plemD : ReifiedPLemma plem.

  Theorem PAPPLY_sound : forall su, rtac_sound (PAPPLY su plem).
  Proof.
    intros.
    unfold PAPPLY.
    apply AT_GOAL_sound; intros.
    remember (get_lemma su plem e).
    destruct o; [apply APPLY_sound; try apply _; try assumption |apply FAIL_sound].
    split; destruct plemD as [H].
    unfold PolyLemmaD in H; simpl in H.
    unfold get_lemma in Heqo.
    forward; inv_all; subst.
    unfold with_typeclasses in H.
    apply inst_sound with (v := v) in H.
    rewrite inst_make_polymorphic in H.
    rewrite H1 in H.
    apply H.
  Qed.

End parameterized.

Hint Opaque PAPPLY : typeclass_instances.

Arguments PAPPLY {tsym func _ _ _ _} unify sym_type_unify lem _ _ _ : rename.
