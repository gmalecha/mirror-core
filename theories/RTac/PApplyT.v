Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Tactics.

Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.PolymorphicF.
Require Import MirrorCore.PLemmaT.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.LemmaApply.
Require Import MirrorCore.UnifyI.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.Reduce.
Require Import MirrorCore.RTac.Apply.
Require Import MirrorCore.RTac.AtGoal.
Require Import MirrorCore.RTac.Fail.

Require Import MirrorCore.Lambda.PolyInstT.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprVariables.

Require Import MirrorCore.Types.ModularTypesT.
Require Import MirrorCore.Types.MTypeUnifyT.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Module PAPPLY (Import RT : TypeLang) (RTU : TypeLangUnify with Module RT := RT).
  Module PI := PolyInst RT RTU.

  Section parameterized.
    Context {tsym : kind -> Type}
            {TSym_tsym : TSym kindD tsym}
            {func : Type}.
    Let typ := type tsym Kstar.

    Let RType_type : RType (type tsym Kstar) := _.
    Let RTypeOk_type : RTypeOk := _.
    Context {RSym_func : RSym func}.
    Context {Typ2_Fun : Typ2 _ RFun}.
    Context {Typ2OkFun : Typ2Ok Typ2_Fun}.
    Context {RTypeOk_typ : RTypeOk}.
    Context {Typ0_Prop : Typ0 _ Prop}.

    Context {RSymOk_func : RSymOk RSym_func}.

    Local Existing Instance Subst_ctx_subst.
    Local Existing Instance SubstOk_ctx_subst.
    Local Existing Instance SubstUpdate_ctx_subst.
    Local Existing Instance SubstUpdateOk_ctx_subst.
    Local Existing Instance Expr_expr.
    Local Existing Instance ExprOk_expr.
    Local Existing Instance ExprUVar_expr.
    Local Existing Instance ExprUVarOk_expr.

    Variable exprUnify : forall subst,
        Subst subst (expr typ func) -> SubstUpdate subst (expr typ func) ->
        unifier typ (expr typ func) subst.

    Variable exprUnify_sound
    : forall subst (S : Subst subst (expr typ func))
              (SO : SubstOk subst typ (expr typ func))
              SU
              (SUO : SubstUpdateOk subst typ (expr typ func)),
        unify_sound (@exprUnify subst S SU).

    Local Definition get_lemma (su : PI.sym_unifier)
          (plem : @PolyLemma kind Kstar (type tsym) (expr typ func) (expr typ func))
          (e : expr typ func)
    : option (lemma typ (expr typ func) (expr typ func)) :=
      match
        PI.get_inst su (@concl _ _ _) plem.(p_lem) e
      with
      | None => None
      | Some args =>
        if (inst (p_tc plem) args)
        then Some (inst (p_lem plem) args)
        else None
      end.

    Definition PAPPLY (su : PI.sym_unifier)
               (plem : @PolyLemma kind Kstar (type tsym) (expr typ func) (expr typ func))
    : rtac typ (expr typ func) :=
      AT_GOAL (fun _ c gl =>
                 match get_lemma su plem gl with
                 | None => FAIL
                 | Some lem => APPLY exprUnify lem
                 end).

    Class ReifiedPLemma (L : @PolyLemma kind Kstar (type tsym) (expr typ func) (expr typ func))
    : Prop := mkRPL
    { ReifiedPLemma_proof : PolyLemmaD (@exprD_typ0 _ _ _ _ Prop _) L }.


    Variable plem : @PolyLemma kind Kstar (type tsym) (expr typ func) (expr typ func).
    Hypothesis plemD : ReifiedPLemma plem.

    Theorem PAPPLY_sound : forall su, rtac_sound (PAPPLY su plem).
    Proof.
      intro.
      unfold PAPPLY.
      apply AT_GOAL_sound; intros.
      remember (get_lemma su plem e).
      destruct o; [apply APPLY_sound; try apply _; try assumption |apply FAIL_sound].
      split; destruct plemD as [H].
      unfold PolyLemmaD in H; simpl in H.
      unfold get_lemma in Heqo.
      symmetry in Heqo.
      forwardy.
      unfold with_typeclasses in H.
      eapply inst_sound with (v:=y) in H.
      rewrite inst_make_polymorphic in H.
      destruct (inst (p_tc plem) y); try solve [ inversion H1 ].
      inv_all. subst.
      assumption.
    Qed.

  End parameterized.

  Hint Opaque PAPPLY : typeclass_instances.

  Arguments PAPPLY {tsym _ func _ _ _ } unify sym_unify lem _ _ _ : rename.

End PAPPLY.