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
  Context {SubstInstantiatable_subst : SubstInstantiatable subst expr}.
  Context {SubstInstantiatableOk_subst : @SubstInstantiatableOk _ _ _ _ Expr_expr Subst_subst _ _}.


  Variable UVar : nat -> expr.
  Variable vars_to_uvars : nat -> nat -> expr -> expr.
  Variable exprUnify : forall subst, Subst subst expr -> SubstUpdate subst expr ->
    tenv typ -> tenv typ -> nat -> expr -> expr -> typ -> subst -> option subst.
  Variable instantiate : (nat -> option expr) -> nat -> expr -> expr.

  Variable lem : Lemma.lemma typ expr expr.

  Definition EAPPLY : rtac typ expr subst :=
    let len_vars := length lem.(vars) in
    fun tus tvs nus nvs ctx sub goal =>
      match @eapplicable typ _ expr _
                         (ctx_subst subst (CExs ctx lem.(vars)))
                         vars_to_uvars (@exprUnify _ _ _)
                         (@ExsSubst _ _ _ lem.(vars) ctx sub (@subst_empty _ _ _))
                         tus tvs lem goal
      with
        | None => Fail
        | Some sub' =>
          let premises :=
              map (fun e => GGoal (vars_to_uvars 0 nus e)) lem.(premises)
          in
          reduceGoal instantiate UVar
                     ctx (CExs CTop lem.(vars)) sub'
                     (GConj_list premises) (len_vars + nus) nvs
      end.

  Hypothesis lemD :
    @Lemma.lemmaD typ expr _ _ expr (@exprD'_typ0 _ _ _ _ Prop _)
                  _ nil nil lem.

  Theorem EAPPLY_sound : rtac_sound nil nil EAPPLY.
  Proof.
  Admitted.

End parameterized.
