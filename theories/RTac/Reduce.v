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
      | GConj_ a b =>
        GConj_ (instantiateGoal f a) (instantiateGoal f b)
    end.

  Fixpoint toGoal (ctx : Ctx typ expr) (cs : ctx_subst subst ctx) (g : Goal typ expr)
           (su : nat)
           (un vn : nat)
  : Result subst CTop :=
    match cs with
      | TopSubst s => More_ (TopSubst _ _ s) g
      | AllSubst t ctx' cs' =>
        match vn with
          | 0 => (** STUCK **)
            Fail
          | S vn' =>
            toGoal cs' (GAll t g) 0 un vn'
        end
      | ExsSubst ts _ cs' s =>
        match un with
          | 0 => (** STUCK **)
            Fail
          | S un' =>
            let nes := forgets un' ts s in
            toGoal cs' (GExs (List.combine ts nes) g) (S su) un' vn
        end
      | HypSubst h _ cs' =>
        toGoal cs' (GHyp h g) 0 un vn
    end.

  (** This assumes that the goal is a [GSolved] **)
  Fixpoint solveGoal (ctx : Ctx typ expr) (cs : ctx_subst subst ctx)
           (su : nat) (un vn : nat)
  : Result subst CTop :=
    match cs with
      | TopSubst s => Solved (TopSubst _ _ s)
      | AllSubst t ctx' cs' =>
        match vn with
          | 0 => (** STUCK **)
            Fail
          | S vn' =>
            (** TODO: Drop var **)
            solveGoal cs' su un vn'
        end
      | ExsSubst ts _ cs' s =>
        match un with
          | 0 => (** STUCK **)
            Fail
          | S un' =>
            let nes := forgets un' ts s in
            toGoal cs' (GExs (List.combine ts nes) GSolved) (S su) un' vn
        end
      | HypSubst h _ cs' =>
        solveGoal cs' 0 un vn
    end.

  Definition reduceGoal (ctx : Ctx typ expr) (s : ctx_subst _ ctx) (g : Goal typ expr)
           (un vn : nat)
  : Result subst CTop :=
    match g with
      | GSolved => solveGoal s 0 un vn
      | _ => toGoal s g 0 un vn
    end.

End parameterized.
