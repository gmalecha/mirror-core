Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Tactics.
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

  Variable UVar : nat -> expr.

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
      | GConj_ ps =>
        GConj (List.map (instantiateGoal f) ps)
    end.

  Fixpoint toGoal (ctx : Ctx typ expr) (s : subst) (g : Goal typ expr)
           (su : nat)
           (un vn : nat)
  : Result typ expr subst :=
    match ctx with
      | CTop => More s g
      | CAll ctx' l =>
        match vn with
          | 0 => (** STUCK **)
            Fail
          | S vn' =>
            (** TODO: Drop var **)
            if strengthenU un su s then
              if strengthenV vn' 1 s then
                toGoal ctx' s g 0 un vn'
              else
                Fail
            else
              Fail
        end
      | CEx  ctx' l =>
        match un with
          | 0 => (** STUCK **)
            Fail
          | S un' =>
            let '(s',ne) := forget un' s in
            match ne with
              | None =>
                toGoal ctx' s' (GEx l ne g) (S su) un' vn
              | Some e =>
                let g' :=
                    instantiateGoal
                      (fun u => if u ?[ eq ] un' then Some e
                                else
                                  if u ?[ gt ] un' then
                                    Some (UVar (u - 1))
                                  else
                                    None) g
                in
                toGoal ctx' s' (* (GEx l (Some e) *) g' (S su) un' vn
            end
        end
      | CHyp ctx' h =>
        if strengthenU un su s then
          toGoal ctx' s (GHyp h g) 0 un vn
        else
          Fail
    end.

  (** This assumes that the goal is a [GSolved] **)
  Fixpoint solveGoal (ctx : Ctx typ expr) (s : subst)
           (su : nat) (un vn : nat)
  : Result typ expr subst :=
    match ctx with
      | CTop =>
        if strengthenU un su s then
          Solved s
        else
          Fail
      | CAll ctx' l =>
        match vn with
          | 0 => (** STUCK **)
            Fail
          | S vn' =>
            (** TODO: Drop var **)
            if strengthenU un su s then
              if strengthenV vn' 1 s then
                solveGoal ctx' s su un vn'
              else
                Fail
            else
              Fail
        end
      | CEx  ctx' l =>
        match un with
          | 0 => (** STUCK **)
            Fail
          | S un' =>
            let '(s',ne) := forget un' s in
            match ne with
              | None =>
                toGoal ctx' s' (GEx l None GSolved) (S su) un' vn
              | Some e =>
                (** NOTE: I don't need to check that [e] is fully
                 ** instantiated because if it is not instantiated
                 ** then when I get to the variable that instantiates
                 ** it, it will not be filled in.
                 **)
                solveGoal ctx' s' (S su) un' vn
            end
        end
      | CHyp ctx' h =>
        if strengthenU un su s then
          solveGoal ctx' s 0 un vn
        else
          Fail
    end.

  Definition reduceGoal (ctx : Ctx typ expr) (s : subst) (g : Goal typ expr)
           (un vn : nat)
  : Result typ expr subst :=
    match g with
      | GSolved => solveGoal ctx s 0 un vn
      | _ => toGoal ctx s g 0 un vn
    end.

  Definition more_list (ctx : Ctx typ expr) (sub : subst)
             (gls : list (Goal typ expr))
  : Result typ expr subst :=
    reduceGoal ctx sub (GConj gls) (countUVars ctx) (countVars ctx).

End parameterized.
