Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.Lambda.ExprCore.
Require Import McExamples.Simple.Simple.
Require Coq.Numbers.BinNums.

(** Declare patterns **)
Reify Declare Patterns patterns_simple_typ := typ.
Reify Declare Patterns patterns_simple := (expr typ func).

About Patterns.

Reify Declare Syntax reify_simple_typ :=
  { (@Patterns _ patterns_simple_typ (@Fail typ)) }.

Reify Declare Typed Table table_terms : BinNums.positive => reify_simple_typ.

(** Declare syntax **)
Reify Declare Syntax reify_simple :=
  { (@Patterns.Patterns _ patterns_simple
    (@Patterns.App _ (@ExprCore.App typ func)
    (@Patterns.Abs (expr typ func) reify_simple_typ (@ExprCore.Abs typ func)
    (@Patterns.Var (expr typ func) (@ExprCore.Var typ func)
    (@Patterns.Fail (expr typ func))))))
    }.

Reify Pattern patterns_simple_typ += (@RExact _ nat)  => tyNat.
Reify Pattern patterns_simple_typ += (@RExact _ bool) => tyBool.
Reify Pattern patterns_simple_typ += (@RExact _ Prop) => tyProp.
Reify Pattern patterns_simple_typ += (@RImpl (@RGet 0 RIgnore) (@RGet 1 RIgnore)) => (fun (a b : function reify_simple_typ) => tyArr a b).

Reify Pattern patterns_simple += (@RGet 0 RConst) => (fun (n : id nat) => @Inj typ func (N n)).
Reify Pattern patterns_simple += (RApp (RApp (@RExact _ plus) (RGet 0 RIgnore)) (RGet 1 RIgnore)) => (fun (a b : function reify_simple) => App (App (Inj Plus) a) b).
Reify Pattern patterns_simple += (RApp (RApp (@RExact _ NPeano.ltb) (RGet 0 RIgnore)) (RGet 1 RIgnore)) => (fun (a b : function reify_simple) => App (App (Inj Lt) a) b).
Reify Pattern patterns_simple += (RApp (RApp (RApp (@RExact _ (@eq)) (RGet 0 RIgnore)) (RGet 1 RIgnore)) (RGet 2 RIgnore)) => (fun (t : function reify_simple_typ) (a b : function reify_simple) => App (App (Inj (Eq t)) a) b).

Ltac reify_typ trm :=
  let k e :=
      refine e
  in
  reify_expr reify_simple_typ k [ ] [ trm ].

Ltac reify trm :=
  let k e :=
      refine e
  in
  reify_expr reify_simple k [ ] [ trm ].

Definition test_typ : typ.
  reify_typ (nat -> nat).
Defined.
Print test_typ.

Definition test_typ_2 : typ.
  reify_typ ((nat -> nat) -> nat -> (nat -> nat -> nat -> nat)).
Defined.
Print test_typ_2.

Definition test_1 : expr typ func.
  reify (0 = 0).
Defined.
Print test_1.

Definition test_2 : expr typ func.
  reify ((NPeano.ltb 0 1) = (NPeano.ltb 0 0)).
Defined.
Print test_2.

Definition test_3 : expr typ func.
  reify ((fun x => x) 1).
Defined.
Print test_3.

Definition test_4 : expr typ func.
  reify ((fun x => x) 1).
Defined.
Print test_4.

Definition test_5 : expr typ func.
  reify ((fun x y => x) 1 3).
Defined.
Print test_5.

Definition test_6 : expr typ func.
  reify ((fun x : nat => x) = (fun y : nat => y)).
Defined.
Print test_6.

Axiom Forall : typ -> func.

Reify Pattern patterns_simple += (RPi (RGet 0 RIgnore) (RGet 1 RIgnore)) => (fun (t : function reify_simple_typ) (b : function reify_simple) => (App (Inj (Forall t)) (Abs t b))).

Definition test_7 : expr typ func.
  reify (forall x : nat, (x + 1) = 1).
Defined.
Print test_7.