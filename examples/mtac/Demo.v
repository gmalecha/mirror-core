Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.Monads.IdentityMonad.
Require Import MirrorCore.Ext.Expr.
Require Import mtac.Patterns.
Require Import mtac.McMtac.

Set Implicit Arguments.
Set Strict Implicit.

Import MonadNotation.
Import McMtacNotation.

Definition test (t : expr) : McMtacT ident (option expr) :=
  mmatch t with
    | [ PApp (PFunc 1 nil) (PGet 0 (tvType 0)) ] =>> fun x => ret (Some x)
    \ ret None
  end%mcmtac.

Let tfs :=
  from_tlist ({| tfenv := 0 ; tftype := tvArr (tvType 0) (tvType 0) |} ::
              {| tfenv := 0 ; tftype := tvType 0 |} :: nil).
Let tus : list typ := nil.
Let tvs := (tvType 0 :: nil).
Let exp := (App (Func 1 nil) (Var 0)).

Eval compute in unIdent (runMcMtac tfs tus tvs 10 (test exp)).
