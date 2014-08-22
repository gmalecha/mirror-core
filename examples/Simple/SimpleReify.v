Add LoadPath "../../src".
Add LoadPath "../../../src".

Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.Lambda.ExprCore.
Require Import McExamples.Simple.Simple.

Axiom reify_simple_typ : Set.
Axiom reify_simple : Set.




Print Simple.

Add Reification Hint (@RExact _ nat) => tyNat : reify_simple_typ.
Add Reification Hint (@RExact _ bool) => tyBool : reify_simple_typ.
Add Reification Hint (@RExact _ Prop) => tyProp : reify_simple_typ.
Add Reification Hint (RApp (RApp (@RExact _ plus) (RGet 0)) (RGet 1)) => (fun (a b : expr typ func) => App (App (Inj Plus) a) b) : reify_simple.