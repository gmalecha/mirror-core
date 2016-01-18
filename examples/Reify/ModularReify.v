Require Import MirrorCore.Reify.Reify.

Reify Declare Patterns patterns_nat : nat.
Reify Declare Patterns patterns_bool : bool.

Inductive nat_or_bool :=
| Nat : nat -> nat_or_bool
| Bool : bool -> nat_or_bool.

Local Notation "x @ y" := (@RApp x y) (only parsing, at level 30).
Local Notation "'!!' x" := (@RExact _ x) (only parsing, at level 25).
Local Notation "'?' n" := (@RGet n RIgnore) (only parsing, at level 25).
Local Notation "'?!' n" := (@RGet n RConst) (only parsing, at level 25).
Local Notation "'#'" := RIgnore (only parsing, at level 0).


Reify Pattern patterns_bool += (!! true) => true.
Reify Pattern patterns_bool += (!! false) => false.

Reify Pattern patterns_nat += (!! 1) => 1.
Reify Pattern patterns_nat += (!! 0) => 0.

Require Import List.

Reify Declare Syntax reify_nat_or_bool :=
  (Patterns.CFirst (   (Patterns.CMap Nat (Patterns.CPatterns patterns_nat))
                    :: (Patterns.CMap Bool (Patterns.CPatterns patterns_bool))
                    :: nil)).

Ltac reify trm :=
  let k e :=
      pose e
  in
  reify_expr reify_nat_or_bool k [[ True ]] [[ trm ]].

Goal True.
  reify 0.
  reify 1.
  reify true.
  reify false.
  exact I.
Qed.