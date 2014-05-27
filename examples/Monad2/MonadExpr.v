Require Import MirrorCore.SymI.
Require Import MirrorCore.SymEnv.
Require Import MirrorCore.Lambda.Expr.
Require Export MirrorCore.Examples.Monad2.MonadTypes.
Require Import MirrorCore.Examples.Monad2.MonadSym.

Set Implicit Arguments.
Set Strict Implicit.

Definition mext : Type := (SymEnv.func + mfunc)%type.

Definition mexpr := expr typ mext.
