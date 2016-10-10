Require Import Coq.Lists.List.
Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.MTypes.ModularTypes.
Require Import MirrorCore.Lambda.ExprCore.
Require Import McExamples.PolyRewrite.QuantifierPuller.MSimple.

(** Declare patterns **)
Reify Declare Patterns patterns_simple_typ : typ.
Reify Declare Patterns patterns_simple : (expr typ func).

Reify Declare Syntax reify_simple_typ :=
  CPatterns patterns_simple_typ.

Axiom otherFunc : BinNums.positive -> expr typ func.

Reify Declare Typed Table table_terms : BinNums.positive => typ.

(** Declare syntax **)
Reify Declare Syntax reify_simple :=
  CFix
    (CFirst (CPatterns patterns_simple ::
             CApp (CRec 0) (CRec 0) (@ExprCore.App typ func) ::
             CAbs (CCall reify_simple_typ) (CRec 0) (@ExprCore.Abs typ func) ::
             CVar (@ExprCore.Var typ func) ::
             CMap otherFunc (CTypedTable (CCall reify_simple_typ) table_terms)
             :: nil)).

Local Notation "x @ y" := (@RApp x y) (only parsing, at level 30).
Local Notation "'!!' x" := (@RExact _ x) (only parsing, at level 25).
Local Notation "'?' n" := (@RGet n RIgnore) (only parsing, at level 25).
Local Notation "'?!' n" := (@RGet n RConst) (only parsing, at level 25).
Local Notation "'#'" := RIgnore (only parsing, at level 0).

Reify Pattern patterns_simple_typ += (!! nat)  => (tyBase0 tyNat).
Reify Pattern patterns_simple_typ += (!! bool) => (tyBase0 tyBool).
Reify Pattern patterns_simple_typ += (!! Prop) => (@tyProp typ').
Reify Pattern patterns_simple_typ += (@RImpl (@RGet 0 RIgnore) (@RGet 1 RIgnore)) => (fun (a b : function (CCall reify_simple_typ)) => tyArr a b).

Reify Pattern patterns_simple += (@RGet 0 RConst) => (fun (n : @id nat) => @Inj typ func (N n)).
Reify Pattern patterns_simple += (!! plus) => (Inj (typ:=typ) Plus).
Reify Pattern patterns_simple += (!! NPeano.Nat.ltb) => (Inj (typ:=typ) Lt).
Reify Pattern patterns_simple += (!! @eq @ ?0) =>
(fun (t : function (CCall reify_simple_typ)) => Inj (typ:=typ) (Eq t)).
Reify Pattern patterns_simple += (RPi (?0) (?1)) =>
  (fun (t : function (CCall reify_simple_typ))
       (b : function (CCall reify_simple)) =>
     (App (Inj (All t)) (Abs t b))).
Reify Pattern patterns_simple += (!! @ex @ ?0) =>
  (fun (t : function (CCall reify_simple_typ)) => Inj (typ:=typ) (Ex t)).
Reify Pattern patterns_simple += (!! and) => (Inj (typ:=typ) And).
Reify Pattern patterns_simple += (!! or) => (Inj (typ:=typ) Or).
Reify Pattern patterns_simple += (!! Basics.impl) => (Inj (typ:=typ) Impl).

Instance Reify_expr_simple : Reify (expr typ func) :=
{ reify_scheme := CCall reify_simple }.

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
  reify_expr reify_simple k [[ True ]] [[ trm ]].

Ltac reify_simple trm k :=
  reify_expr reify_simple k [[ True ]] [[ trm ]].


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
  reify ((NPeano.Nat.ltb 0 1) = (NPeano.Nat.ltb 0 0)).
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

Definition test_7 : expr typ func.
  reify (forall x : nat, 1 = 1 -> (x + 1) = 1).
Defined.
Print test_7.

(** Something that doesn't fit **)
Definition id T (x : T) : T := x.

Definition test_fail : expr typ func.
  reify (id nat 0).
Defined.
Print test_fail.

Definition foo : nat := 6.
Reify Seed Typed Table table_terms += 1 => [[ MSimple.tyNat , foo ]].

Definition test_table : expr typ func.
  reify (foo).
Defined.
Print test_table.
