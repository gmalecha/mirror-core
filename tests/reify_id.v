Require Import MirrorCore.Reify.Reify.
Require Import Coq.Lists.List.

Inductive expr :=
| Abs : expr -> expr
| Var : nat -> expr
| Nat : nat -> expr.

Reify Declare Patterns ptrns := expr.

Reify Declare Syntax reify_t :=
{ (@Patterns.CPatterns expr ptrns) }.

Reify Declare Syntax reify_expr :=
{ (@Patterns.CFirst _ ((@Patterns.CPatterns expr ptrns) ::
                       (@Patterns.CAbs expr reify_t (fun _ => Abs)) ::
                       (@Patterns.CVar expr Var) :: nil))
  }.

Reify Pattern ptrns += (@RExact _ nat)  => (Nat 0).
Reify Pattern ptrns += (@RHasType nat (@RGet 0 RIgnore)) => (fun a : id nat => Nat a).

Ltac reify trm :=
  let k e :=
      pose e
  in
  reify_expr reify_expr k [ True ] [ trm ].

Goal True.
  reify (fun x : nat => x).
  exact I.
Qed.