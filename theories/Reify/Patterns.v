Definition table    (K V : Type) : Type := prod K V.

(** Patterns **)
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

(** Actions **)
Definition function (f : Type)   : Type := f.
Definition id       (T : Type)   : Type := T.
Definition store    {K V : Type} (t : table K V) : Type := V.

(** Commands **)
Inductive Command :=
| Patterns (T : Type)
| Call (T : Type)
| App {T : Type} (app : T -> T -> T)
| Abs (T : Type) {U : Type} (lam : T -> U -> U)
| Var {T : Type} (var : nat -> T)
| Table (K V : Type) (t : table K V).

(** Suggested Notation **)
(*
Local Notation "x @ y" := (@RApp x y) (only parsing, at level 30).
Local Notation "'!!' x" := (@RExact _ x) (only parsing, at level 25).
Local Notation "'?' n" := (@RGet n RIgnore) (only parsing, at level 25).
Local Notation "'?!' n" := (@RGet n RConst) (only parsing, at level 25).
Local Notation "'#'" := RIgnore (only parsing, at level 0).
*)