Require Import ExtLib.Structures.Monad.
Require Import MirrorCore.Ext.Expr.
Require Import mtac.McMtac.

Set Implicit Arguments.
Set Strict Implicit.

Import MonadNotation.
Import McMtacNotation.

Definition test (t : expr) : McMtac (option expr) :=
  mmatch t with
    | [ App (Func 0 nil) (UVar 0) ] =>> fun x => ret (Some x)
    \ ret None
  end%mcmtac.

Let tfs := {| tfenv := 0 ; tftype := tvArr (tvType 0) (tvType 0) |} ::
           {| tfenv := 0 ; tftype := tvType 0 |} :: nil.
Let tus : list typ := nil.
Let tvs := (tvType 0 :: nil).
Let exp := (App (Func 0 nil) (Var 0)).

Eval compute in runMcMtac tfs tus tvs 10 (test exp).