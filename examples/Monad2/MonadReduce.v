Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.Option.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.Examples.Monad2.MonadExpr.
Require Import MirrorCore.Examples.Monad2.Tests.

Set Implicit Arguments.
Set Strict Implicit.

Local Notation "'BIND' [ a ,  b ]" := (ExprCore.Inj (inr (MonadSym.mBind a b))) (at level 20).
Local Notation "'RETURN' [ a ]" := (ExprCore.Inj (inr (MonadSym.mReturn a))) (at level 20).
Local Notation "a @ b" := (ExprCore.App a b) (at level 18, left associativity).

Definition smart_app (a b : mexpr) : mexpr :=
  a @ b.

Definition smart_bind (a b : typ) (c d : mexpr) : mexpr :=
  match d with
    | RETURN [ _ ] => c
    | _ => match c with
             | ExprCore.Abs _ (RETURN [ _ ] @ c) =>
               smart_app d c
             | _ => BIND [ a , b ] @ c @ d
           end
  end.

(**
The rules are the following
1) (fun x => f x) = f
2) bind (ret x) f = f x
3) bind x ret = x
4) bind (bind a b) c = bind a (fun x => bind (b x) c)
**)
Fixpoint reduce_arrow (d r : typ) (e : mexpr) {struct e} : mexpr :=
  match e with
    | ExprCore.Abs t (ExprCore.App x (ExprCore.Var 0)) =>
      match lower 0 1 x with
        | None => e
        | Some e => e
      end
    | ExprCore.Abs _ e' =>
      match r with
        | tyM m => reduce_m m e'
        | _ => e
      end
    | _ => e
  end
with reduce_m (t : typ) (e : mexpr) {struct e} : mexpr :=
  match e with
    | BIND [ _ , _ ] @ e @ RETURN [ _ ] => reduce_m t e
    | BIND [ t' , _ ] @ (RETURN [ _ ] @ e) @ e' =>
      let e' := reduce_arrow t' (tyM t) e' in
      let e := match t' with
                 | tyM z => reduce_m z e
                 | tyArr a b => reduce_arrow a b e
                 | _ => e
               end in
      e' @ e
    | BIND [ t' , _ ] @ (BIND [ t'' , _ ] @ a @ b) @ c =>
      let a := reduce_m t'' a in
      let b := reduce_arrow t'' (tyM t') b in
      let c := reduce_arrow t' (tyM t) c in
      smart_bind t' t a (ExprCore.Abs t'' (smart_bind t' t (b @ (ExprCore.Var 0)) c))
    | _ => e
  end.

Definition reduce (t : typ) (e : mexpr) : mexpr :=
  match t with
    | tyM a => reduce_m a e
    | tyArr d r => reduce_arrow d r e
    | _ => e
  end.


Eval compute in reduce (tyM demo.tNat) demo.t1.
Eval compute in reduce (tyM demo.tNat) demo.t2.
Eval compute in reduce (tyM demo.tNat) demo.t3.
