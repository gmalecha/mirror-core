Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.LemmaApply.
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
  Variable exprUnify : tenv typ -> tenv typ -> nat -> expr -> expr -> typ -> subst -> option subst.
  Variable instantiate : (nat -> option expr) -> nat -> expr -> expr.

  Let eapplicable :=
    @eapplicable typ _ expr _ subst vars_to_uvars
                 exprUnify.

  Definition EAPPLY
             (lem : Lemma.lemma typ expr expr)
  : rtac typ expr subst :=
    let len_vars := length lem.(vars) in
    fun ctx sub gl =>
      let '(tus,tvs) := getEnvs ctx in
      match eapplicable sub tus tvs lem gl with
        | None => Fail
        | Some sub' =>
          let len_uvars := length tus in
          let premises := map (fun x => GGoal (vars_to_uvars 0 len_uvars x)) lem.(premises) in
          more_list instantiate (fold_left (@CEx _ _) lem.(vars) ctx) sub' premises
      end.

End parameterized.
