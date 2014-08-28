Require Coq.FSets.FMapPositive.

Inductive table (K : Type) : Type := a_table.
Inductive typed_table (K T : Type) : Type := a_typed_table.
Inductive patterns (T : Type) : Type := a_pattern.

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
Definition function  (f : Type)   : Type := f.
Definition id        (T : Type)   : Type := T.
Definition associate {K : Type} (t : table K) (key : K) : Type.
exact unit.
Qed.
Definition store     (K : Type) (t : table K) : Type := K.

(** Commands **)
Inductive Command (T : Type) :=
| Fail
| Patterns (f : patterns T) (_ : Command T)
| Call (f : Type) (_ : Command T)
| App (app : T -> T -> T) (_ : Command T)
| Abs (U : Type) (lam : U -> T -> T) (_ : Command T)
| Var (var : nat -> T) (_ : Command T)
| Table (K : Type) (t : table K) (ctor : K -> T) (_ : Command T)
| TypedTable (K Ty : Type) (t : typed_table K Ty) (ctor : K -> T) (_ : Command T).

(** Tables Reification Specification **)
Definition mk_var_map {K V T : Type} (_ : table K) (ctor : V -> T) : Type :=
  FMapPositive.PositiveMap.t T.
Definition mk_dvar_map {K V T : Type} {F : V -> Type}
              (_ : typed_table K V)
              (ctor : forall x : V, F x -> T) :=
  FMapPositive.PositiveMap.t T.
Definition mk_dvar_map_abs {K V T D : Type} {F : V -> Type}
              (_ : typed_table K V)
              (ctor : forall x : V, F x -> T) :=
  FMapPositive.PositiveMap.t T.

(** Suggested Notation **)
(*
Local Notation "x @ y" := (@RApp x y) (only parsing, at level 30).
Local Notation "'!!' x" := (@RExact _ x) (only parsing, at level 25).
Local Notation "'?' n" := (@RGet n RIgnore) (only parsing, at level 25).
Local Notation "'?!' n" := (@RGet n RConst) (only parsing, at level 25).
Local Notation "'#'" := RIgnore (only parsing, at level 0).
*)