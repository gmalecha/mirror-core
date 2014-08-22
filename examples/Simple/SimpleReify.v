Add LoadPath "../../src".
Add LoadPath "../../../src".

Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.Lambda.ExprCore.
Require Import McExamples.Simple.Simple.

Definition reify_simple_typ := typ.
Definition reify_simple := expr typ func.

Reify: Declare Patterns reify_simple_typ.
Reify: Add Pattern (@RExact _ nat)  => tyNat  : reify_simple_typ.
Reify: Add Pattern (@RExact _ bool) => tyBool : reify_simple_typ.
Reify: Add Pattern (@RExact _ Prop) => tyProp : reify_simple_typ.

Reify: Declare Patterns reify_simple.
Reify: Add Pattern (@RGet 0 RConst) => (fun (n : id nat) => @Inj typ func (N n))  : reify_simple.
Reify: Add Pattern (RApp (RApp (@RExact _ plus) (RGet 0 RIgnore)) (RGet 1 RIgnore)) => (fun (a b : function (reify_simple)) => App (App (Inj Plus) a) b) : reify_simple.
Reify: Add Pattern (RApp (RApp (@RExact _ NPeano.ltb) (RGet 0 RIgnore)) (RGet 1 RIgnore)) => (fun (a b : function (reify_simple)) => App (App (Inj Lt) a) b) : reify_simple.
Reify: Add Pattern (RApp (RApp (RApp (@RExact _ (@eq)) (RGet 0 RIgnore)) (RGet 1 RIgnore)) (RGet 2 RIgnore)) => (fun (t : function reify_simple_typ) (a b : function reify_simple) => App (App (Inj (Eq t)) a) b) : reify_simple.

Reify: Declare Syntax reify_simple_typ { (Patterns reify_simple_typ) }.
Reify: Declare Syntax reify_simple { (Patterns reify_simple)
                                     (@Patterns.App _ (@ExprCore.App typ func))
                                     (@Patterns.Abs reify_simple_typ (expr typ func) (@ExprCore.Abs typ func))
                                     (@Patterns.Var (expr typ func) (@ExprCore.Var typ func)) }.

Ltac reify trm :=
  let k e :=
      refine e
  in
  reify_expr reify_simple k [ trm ].


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