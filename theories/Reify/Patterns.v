Inductive RPattern : Type :=
| RIgnore
| RConst
| RHasType (T : Type) (p : RPattern)
| RGet   (idx : nat) (p : RPattern)
| RApp   (f x : RPattern)
| RPi    (t r : RPattern)
| RImpl  (l r : RPattern)
| RExact {T : Type} (value : T).

Definition function (f : Type) : Type := f.
Definition id       (T : Type) : Type := T.
(*
Axiom reify    : forall (T : Type), function T -> T.
*)

Notation "'?' x" := (RGet x) (at level 30) : reify_pattern.
Notation "'__'" := (RIgnore) (at level 30) : reify_pattern.
Notation "x '@' y" := (RApp x y) (at level 30) : reify_pattern.
Notation "x '->' y" := (RImpl x y) (at level 30) : reify_pattern.



(**
(** Tables **)
Axiom Table : forall (K V : Type), Type.

Axiom get_store : forall {K V : Type} (T : Table K V) (key : K), V.
**)