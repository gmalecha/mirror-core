Require Import Expr.
Require Import Subst.
Require Import Prover.

Set Implicit Arguments.
Set Strict Implicit.

Definition unifier  (ts : types) : Type :=
  forall (S : Type) (Subst_S : Subst ts S) (P : ProverT ts), 
    Facts P ->
    S -> expr ts -> expr ts -> option S.

Definition unifier_WellTyped (ts : types) (fs : tfunctions) (unify : unifier ts) : Prop :=
  forall  (S : Type) (Subst_S : Subst ts S) (P : ProverT ts) 
    (F : Facts P) (subst : S) (e1 e2 : expr ts) subst', 
    unify _ _ P F subst e1 e2 = Some subst' -> True.

Definition unifier_sound (ts : types) (fs : functions ts) (unify : unifier ts) : Prop :=
  forall (S : Type) (Subst_S : Subst ts S) (P : ProverT ts) (PC : ProverT_correct P fs) (F : Facts P) (subst : S) (e1 e2 : expr ts) subst', 
    unify _ _ P F subst e1 e2 = Some subst' -> True.
