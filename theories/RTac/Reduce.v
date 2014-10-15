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

  Fixpoint toGoal (ctx ctx' : Ctx typ expr)
           (cs : ctx_subst subst (Ctx_append ctx ctx')) (g : Goal typ expr)
           (su : nat)
           (un vn : nat)
  : Result subst ctx :=
    match ctx' as ctx'
          return ctx_subst subst (Ctx_append ctx ctx') -> Result subst ctx
    with
      | CTop => fun cs => More_ cs g
      | CAll ctx' t => fun cs =>
        match vn with
          | 0 => (** STUCK **)
            Fail
          | S vn' =>
            @toGoal ctx ctx' (fromAll cs) (GAll t g) 0 un vn'
        end
      | CHyp ctx' h => fun cs =>
        @toGoal ctx ctx'  (fromHyp cs) (GHyp h g) 0 un vn
      | CExs ctx' ts => fun cs =>
        match un with
          | 0 => (** STUCK **)
            Fail
          | S un' =>
            let '(s,cs') := fromExs cs in
            let nes := forgets un' ts s in
            @toGoal ctx ctx' cs' (GExs (List.combine ts nes) g) (S su) un' vn
        end
    end cs.

  (** This assumes that the goal is a [GSolved] **)
  Fixpoint solveGoal (ctx ctx' : Ctx typ expr)
           (cs : ctx_subst subst (Ctx_append ctx ctx'))
           (su : nat) (un vn : nat)
  : Result subst ctx :=
    match ctx' as ctx'
          return ctx_subst subst (Ctx_append ctx ctx') -> Result subst ctx
    with
      | CTop => fun cs => Solved cs
      | CAll ctx' t => fun cs =>
        match vn with
          | 0 => (** STUCK **)
            Fail
          | S vn' =>
            @solveGoal ctx ctx' (fromAll cs) 0 un vn'
        end
      | CHyp ctx' h => fun cs =>
        @solveGoal ctx ctx'  (fromHyp cs) 0 un vn
      | CExs ctx' ts => fun cs =>
        match un with
          | 0 => (** STUCK **)
            Fail
          | S un' =>
            let '(s,cs') := fromExs cs in
            let nes := forgets un' ts s in
            @toGoal ctx ctx' cs' (GExs (List.combine ts nes) GSolved) (S su) un' vn
        end
    end cs.

  Definition reduceGoal (ctx ctx' : Ctx typ expr) (s : ctx_subst _ (Ctx_append ctx ctx'))
             (g : Goal typ expr)
             (un vn : nat)
  : Result subst ctx :=
    match g with
      | GSolved => @solveGoal ctx ctx' s 0 un vn
      | _ => @toGoal ctx ctx' s g 0 un vn
    end.

End parameterized.
