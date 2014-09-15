Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.RTac.Core.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.
  Variable RType_typ : RType typ.
  Variable Expr_expr : Expr RType_typ expr.
  Variable Typ0_Prop : Typ0 _ Prop.
  Variable Subst_subst : Subst subst expr.
  Variable SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst.
  Variable SubstUpdate_subst : SubstUpdate subst expr.
  Variable SubstUpdateOk_subst : @SubstUpdateOk _ _ _ _ Expr_expr Subst_subst _ _.

  Variable (check : Ctx typ expr -> expr -> expr -> subst -> option subst).

  Fixpoint findHyp s (ctx : Ctx typ expr) (g : expr) {struct ctx}
  : option subst :=
    match ctx with
      | CTop => None
      | CAll ctx' _ => findHyp s ctx' g
      | CEx  ctx' _ => findHyp s ctx' g
      | CHyp ctx' h => match check ctx' g h s with
                         | None => findHyp s ctx' g
                         | Some e => Some e
                       end
    end.

  Definition ASSUMPTION : rtac typ expr subst :=
    fun ctx s gl =>
      match findHyp s ctx gl with
        | None => Fail
        | Some s' =>
          Solved s'
      end.

  (** check soundness **)

End parameterized.

(*
  Fixpoint reduceGoal (ctx : Ctx typ expr) (s : subst) (un vn : nat)
  : Ctx typ expr * subst :=
    match ctx with
      | CTop => (ctx, s)
      | CAll ctx' l =>
        match vn with
          | 0 => (** STUCK **)
            (ctx, s)
          | S vn' =>
            (** TODO: Drop var **)
            reduceGoal ctx' s un vn'
        end
      | CEx  ctx' l =>
        match un with
          | 0 => (** STUCK **)
            (ctx, s)
          | S un' =>
            match drop un' s with
              | Some s' =>
                reduceGoal ctx' s' un' vn
              | None => (** STUCK **)
                (ctx, s)
            end
        end
      | CHyp ctx' h =>
        reduceGoal ctx' s un vn
    end.
*)