Require Import ExtLib.Data.PList.

Require Import MirrorCore.Lib.ListView.
Require Import MirrorCore.Lib.NatView.
Require Import MirrorCore.syms.SymOneOf.

Require Import McExamples.PolyApply.MSimpleType.

Import OneOfType.

Definition func_map : 
  OneOfType.pmap :=
  list_to_pmap
    (pcons natFunc
           (pcons (list_func typ) pnil)).