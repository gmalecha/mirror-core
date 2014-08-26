Require Import McExamples.Simple.SimpleReify.

Reify Print Patterns SimpleReify.reify_simple_typ.

Definition test_typ : Simple.typ.
  reify_typ (nat -> nat).
Defined.
Print test_typ.

Definition test_term : ExprCore.expr Simple.typ Simple.func.
  reify (0 = 0).
Defined.
Print test_1.