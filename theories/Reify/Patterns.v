Inductive RPattern : Type :=
| RIgnore
| RConst
| RHasType (T : Type) (p : RPattern)
| RGet   (idx : nat) (p : RPattern)
| RApp   (f x : RPattern)
| RLam   (t r : RPattern)
| RPi    (t r : RPattern)
| RImpl  (l r : RPattern)
| RExact {T : Type} (value : T).

Definition function (f : Type) : Type := f.
Definition id       (T : Type) : Type := T.
Definition table    (K V : Type) : Type := prod K V.

Inductive Command :=
| Patterns (T : Type)
| Call (T : Type)
| App {T : Type} (app : T -> T -> T)
| Abs (T : Type) {U : Type} (lam : T -> U -> U)
| Var {T : Type} (var : nat -> T)
(*| Table (K V : Type) (t : table K V) *).

(*
(** Notation **)
Notation "'?' x" := (RGet x) (at level 30) : reify_pattern.
Notation "'__'" := (RIgnore) (at level 30) : reify_pattern.
Notation "x '@' y" := (RApp x y) (at level 30) : reify_pattern.
Notation "x '->' y" := (RImpl x y) (at level 30) : reify_pattern.
*)
