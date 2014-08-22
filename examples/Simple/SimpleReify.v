Add LoadPath "../../src".
Add LoadPath "../../../src".

Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.Lambda.ExprCore.
Require Import McExamples.Simple.Simple.

Definition reify_simple_typ := typ.
Definition reify_simple := expr typ func.

Print func.

Add Reification Hint (@RExact _ nat)  => tyNat  : reify_simple_typ.
Add Reification Hint (@RExact _ bool) => tyBool : reify_simple_typ.
Add Reification Hint (@RExact _ Prop) => tyProp : reify_simple_typ.

Add Reification Hint (@RGet 0 RConst) => (fun (n : id nat) => @Inj typ func (N n))  : reify_simple.
Add Reification Hint (RApp (RApp (@RExact _ plus) (RGet 0 RIgnore)) (RGet 1 RIgnore)) => (fun (a b : function (reify_simple)) => App (App (Inj Plus) a) b) : reify_simple.
Add Reification Hint (RApp (RApp (@RExact _ NPeano.ltb) (RGet 0 RIgnore)) (RGet 1 RIgnore)) => (fun (a b : function (reify_simple)) => App (App (Inj Lt) a) b) : reify_simple.
Add Reification Hint (RApp (RApp (RApp (@RExact _ (@eq)) (RGet 0 RIgnore)) (RGet 1 RIgnore)) (RGet 2 RIgnore)) => (fun (t : function reify_simple_typ) (a b : function reify_simple) => App (App (Inj (Eq t)) a) b) : reify_simple.

Ltac reify trm :=
  let k e :=
      refine e
  in
  reify_expr reify_simple k [ trm ].


Definition foo : expr typ func.
  reify (0 = 0).
Defined.

Definition foo' : expr typ func.
  reify ((NPeano.ltb 0 1) = (NPeano.ltb 0 0)).
Defined.