Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.InstantiateI.
Require Import MirrorCore.RTac.Core.

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
  Context {SubstUpdate_subst : SubstUpdate subst expr}.
  Context {SubstUpdateOk_subst : @SubstUpdateOk _ _ _ _ Expr_expr Subst_subst _ _}.

  Variable instantiate : (nat -> option expr) -> nat -> expr -> expr.

  Fixpoint instantiateGoal (f : nat -> option expr) (g : Goal typ expr)
  : Goal typ expr :=
    match g with
      | GSolved => GSolved
      | GGoal g => GGoal (instantiate f 0 g)
      | GAll t g' => GAll t (instantiateGoal f g')
      | GExs tes g' => GExs (List.map (fun te =>
                                         match te with
                                           | (t,None) => (t,None)
                                           | (t,Some e) => (t,Some (instantiate f 0 e))
                                         end) tes)
                            (instantiateGoal f g')
      | GHyp h g' => GHyp (instantiate f 0 h) (instantiateGoal f g')
      | GConj ps =>
        GConj (List.map (instantiateGoal f) ps)
    end.

  Fixpoint reduceGoal (ctx : Ctx typ expr) (s : subst) (g : Goal typ expr)
           (un vn : nat)
  : Result typ expr subst :=
    match ctx with
      | CTop => match g with
                  | GSolved => Solved s
                  | g => More s g
                end
      | CAll ctx' l =>
        match vn with
          | 0 => (** STUCK **)
            Fail
          | S vn' =>
            (** TODO: Drop var **)
            reduceGoal ctx' s g un vn'
        end
      | CEx  ctx' l =>
        match un with
          | 0 => (** STUCK **)
            Fail
          | S un' =>
            match drop un' s with
              | None =>
                reduceGoal ctx' s (GEx l (lookup un' s) g) un' vn
              | Some s' =>
                match lookup un' s with
                  | None => Fail (** DEAD **)
                  | Some e =>
                    (** NOTE: If this gets removed then all of the variables
                     ** have to be renumbered. This is because this is
                     ** actually a subst, not an instantiate
                     **)
                    let g' := instantiateGoal(fun u => if u ?[ eq ] un' then Some e else None) g
                    in
                    match g' with
                      | GSolved =>
                        reduceGoal ctx' s' g' un' vn
                      | _ => reduceGoal ctx' s' (GEx l (Some e) g') un' vn
                    end
                end
            end
        end
      | CHyp ctx' h =>
        reduceGoal ctx' s g un vn
    end.

  Definition more_list (ctx : Ctx typ expr) (sub : subst)
             (gl : list (Goal typ expr))
  : Result typ expr subst :=
    reduceGoal ctx sub match gl with
                         | nil => GSolved
                         | _ :: _ => GConj gl
                       end (countUVars ctx) (countVars ctx).

End parameterized.
