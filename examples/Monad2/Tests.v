Require Import ExtLib.Structures.Monad.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Examples.Monad2.MonadExpr.

Set Implicit Arguments.
Set Strict Implicit.

Module demo.

  Definition tNat := tyType 1.
  Definition tBool := tyType 2.
  Let eBind (a b : typ) : mexpr := ExprCore.Inj (inr (MonadSym.mBind a b)).
  Let eReturn (a : typ) : mexpr := ExprCore.Inj (inr (MonadSym.mReturn a)).
  Let e_ (p : positive) : mexpr := ExprCore.Inj (inl p).
  Let bind_ (a b : typ) (c d : mexpr) : mexpr :=
    App (App (eBind a b) c) d.
  Let ret_ (a : typ) (b : mexpr) : mexpr :=
    App (eReturn a) b.

  Definition t1 : mexpr :=
    bind_ tNat tNat (e_ 2) (eReturn tNat).

  Definition t2 : mexpr :=
    bind_ tNat tNat (ret_ tNat (e_ 1)) (e_ 3).

  Definition t3 : mexpr :=
    bind_ tNat tNat (bind_ tNat tNat (e_ 2) (e_ 3)) (e_ 3).

End demo.
