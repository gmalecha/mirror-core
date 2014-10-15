Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.LemmaApply.
Require Import MirrorCore.InstantiateI.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.Reduce.

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
  Context {SU : SubstUpdate subst expr}.
  Context {SubstUpdateOk_subst : @SubstUpdateOk _ _ _ _ Expr_expr Subst_subst _ _}.

  Variable vars_to_uvars : nat -> nat -> expr -> expr.
  Variable exprUnify : forall subst, Subst subst expr -> SubstUpdate subst expr ->
    tenv typ -> tenv typ -> nat -> expr -> expr -> typ -> subst -> option subst.
  Variable instantiate : (nat -> option expr) -> nat -> expr -> expr.
  Variable UVar : nat -> expr.

  Variable lem : Lemma.lemma typ expr expr.

  Definition EAPPLY : rtac typ expr subst :=
    let len_vars := length lem.(vars) in
    fun tus tvs nus nvs ctx sub goal =>
      match @eapplicable typ _ expr _
                         (ctx_subst subst (CExs ctx lem.(vars)))
                         vars_to_uvars (@exprUnify _ _ _)
                         (@ExsSubst _ _ _ lem.(vars) ctx sub (@empty _ _ _))
                         tus tvs lem goal
      with
        | None => Fail
        | Some sub' =>
          let len_uvars := length tus in
          let premises := map (fun x => GGoal (vars_to_uvars 0 len_uvars x)) lem.(premises) in
          reduceGoal instantiate UVar (fold_left (@CEx _ _) lem.(vars) CTop) sub'
                     (GConj premises) (countUVars ctx + len_vars) (countVars ctx)
      end.

  Let tyProp := @typ0 _ _ Prop _.

  Let cast (e : typD tyProp) : Prop :=
    match @typ0_cast typ _ Prop _ in _ = T return T with
      | eq_refl => e
    end.

  Hypothesis lemD :
    @Lemma.lemmaD typ _ expr _ expr (@exprD'_typ0 _ _ _ _ Prop _)
                  tyProp cast nil nil lem.

  Theorem EAPPLY_sound : rtac_sound nil nil EAPPLY.
  Proof.
  Admitted.

End parameterized.
