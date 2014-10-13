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
  Variable exprUnify :
    tenv typ -> tenv typ -> nat -> expr -> expr -> typ -> subst -> option subst.
  Variable instantiate : (nat -> option expr) -> nat -> expr -> expr.
  Variable UVar : nat -> expr.

  Let eapplicable :=
    @eapplicable typ _ expr _ subst vars_to_uvars
                 exprUnify.

  Definition APPLY
             (lem : Lemma.lemma typ expr expr)
  : rtac typ expr subst :=
    let len_vars := length lem.(vars) in
    fun ctx sub goal =>
      let '(tus,tvs) := getEnvs ctx in
      match eapplicable sub tus tvs lem goal with
        | None => Fail
        | Some sub' =>
          let len_uvars := length tus in
          match pull (expr := expr) (SU := SU) len_uvars len_vars sub' with
            | Some sub'' =>
              let premises :=
                  map (fun e => instantiate (fun u => lookup u sub') 0
                                            (vars_to_uvars 0 len_uvars e))
                      lem.(premises)
              in
              more_list instantiate UVar CTop sub'' (map GGoal premises)
              (** Solve the side conditions **)
            | None => Fail
          end
      end.

End parameterized.
