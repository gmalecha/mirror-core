Require Import Coq.Lists.List.
Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.MTypes.ModularTypes.
Require Import MirrorCore.Lambda.ExprCore.
Require Import McExamples.Tauto.MSimpleTyp.
Require Import McExamples.Tauto.ILogic.
Require Import McExamples.Tauto.ILogicFunc.

Require Import MirrorCore.PLemma.
Require Import MirrorCore.RTac.PApply.
Require Import MirrorCore.Lambda.ExprUnify_simple.

(** Declare patterns **)
Reify Declare Patterns patterns_simple_typ : typ.
Reify Declare Patterns patterns_ilfunc : (expr typ ilfunc).

Reify Declare Syntax reify_simple_typ :=
  CPatterns patterns_simple_typ.

Axiom otherFunc : BinNums.positive -> expr typ ilfunc.

Reify Declare Typed Table table_terms : BinNums.positive => typ.

(** Declare syntax **)
Reify Declare Syntax reify_ilfunc :=
  CFix
    (CFirst (CPatterns patterns_ilfunc ::
             CApp (CRec 0) (CRec 0) (@ExprCore.App typ ilfunc) ::
             CAbs (CCall reify_simple_typ) (CRec 0) (@ExprCore.Abs typ ilfunc) ::
             CVar (@ExprCore.Var typ ilfunc) ::
             CMap otherFunc (CTypedTable (CCall reify_simple_typ) table_terms)
             :: nil)).

Local Notation "x @ y" := (@RApp x y) (only parsing, at level 30).
Local Notation "'!!' x" := (@RExact _ x) (only parsing, at level 25).
Local Notation "'?' n" := (@RGet n RIgnore) (only parsing, at level 25).
Local Notation "'?!' n" := (@RGet n RConst) (only parsing, at level 25).
Local Notation "'#'" := RIgnore (only parsing, at level 0).

Reify Pattern patterns_simple_typ += (!! nat)  => (tyNat).
Reify Pattern patterns_simple_typ += (!! bool) => (tyBool).
Reify Pattern patterns_simple_typ += (!! Prop) => (tyProp).
Reify Pattern patterns_simple_typ += (@RImpl (@RGet 0 RIgnore) (@RGet 1 RIgnore)) => (fun (a b : function (CCall reify_simple_typ)) => tyArr a b).

Reify Pattern patterns_ilfunc += (!! @ILogic.ltrue @ ?0 @ #) =>
  (fun (x : function (CCall reify_simple_typ)) => mkTrue x).
Reify Pattern patterns_ilfunc += (!! @ILogic.lfalse @ ?0 @ #) =>
  (fun (x : function (CCall reify_simple_typ)) => mkFalse x).
Reify Pattern patterns_ilfunc += (!! @ILogic.land @ ?0 @ #) =>
  (fun (x : function (CCall reify_simple_typ)) => Inj (typ := typ) (fAnd x)).
Reify Pattern patterns_ilfunc += (!! @ILogic.lor @ ?0 @ #) =>
  (fun (x : function (CCall reify_simple_typ)) => Inj (typ := typ) (fOr x)).
Reify Pattern patterns_ilfunc += (!! @ILogic.limpl @ ?0 @ #) =>
  (fun (x : function (CCall reify_simple_typ)) => Inj (typ := typ) (fImpl x)).
Reify Pattern patterns_ilfunc += (!! @ILogic.lentails @ ?0 @ #) =>
  (fun (x : function (CCall reify_simple_typ)) => Inj (typ := typ) (fEntails x)).
Reify Pattern patterns_ilfunc += (!! @ILogic.lexists @ ?0 @ # @ ?1) => (fun (x y : function (CCall reify_simple_typ)) => Inj (typ := typ) (fExists y x)).
Reify Pattern patterns_ilfunc += (!! @ILogic.lforall @ ?0 @ # @ ?1) => (fun (x y : function (CCall reify_simple_typ)) => Inj (typ := typ) (fForall y x)).

Instance Reify_expr_ilfunc : Reify (expr typ ilfunc) :=
{ reify_scheme := CCall reify_ilfunc }.

Instance Reify_simple_type : Reify typ :=
{ reify_scheme := CCall reify_simple_typ }.

Ltac reify_typ trm :=
  let k e :=
      refine e
  in
  reify_expr reify_simple_typ k [[ True ]] [[ trm ]].

Ltac reify trm :=
  let k e :=
      refine e
  in
  reify_expr reify_ilfunc k [[ True ]] [[ trm ]].

Ltac reify_ilfunc trm k :=
  reify_expr reify_ilfunc k [[ True ]] [[ trm ]].


Definition test_typ : typ.
  reify_typ (nat -> nat).
Defined.
Print test_typ.

Definition test_typ_2 : typ.
  reify_typ ((nat -> nat) -> nat -> (nat -> nat -> nat -> nat)).
Defined.
Print test_typ_2.

Definition test_1 : expr typ ilfunc.
  reify (@ltrue Prop _).
Defined.
Print test_1.

Definition test_2 : expr typ ilfunc.
  reify (@lfalse Prop _).                      
Defined.
Print test_2.

Definition test_3 : expr typ ilfunc.
  reify (@land Prop _ (@ltrue Prop _) (@lfalse Prop _)).
Defined.
Print test_3.

Definition test_4 (P : nat -> Prop) : expr typ ilfunc.
  reify (@lexists Prop _ nat P).
Defined.
Print test_4.
