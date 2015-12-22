Require Coq.FSets.FMapPositive.

Unset Elimination Schemes.

(* NOTE: These should realy be axioms **)
Inductive table (K : Type) : Type := a_table.
Inductive typed_table (K T : Type) : Type := a_typed_table.
Inductive patterns (T : Type) : Type := a_pattern.

(** Commands **)
(* Command T parses a constr into a T *)
Inductive Command (T : Type) :=
| CPatterns   (f : patterns T)
| CApp        (app : T -> T -> T)
| CAbs        {U : Type} (c : Command U) (lam : U -> T -> T)
| CVar        (var : nat -> T)
| CTable      (t : table T)
| CTypedTable {Ty : Type} (cTy : Command Ty) (t : typed_table T Ty)
| CMap        {F : Type} (f : F -> T) (c : Command F)
| COr         (a b : Command T)
| CFail.

Arguments CPatterns {_} _.
Arguments CApp {_} _.
Arguments CAbs {_ _} _ _.
Arguments CVar {_} _.
Arguments CTable {_} _.
Arguments CTypedTable {_ _} _ _.
Arguments CMap {_ _} _ _.
Arguments CFail {_}.
Arguments COr {_} _ _.

Fixpoint CFirst {T} (ls : list (Command T)) : Command T :=
  match ls with
  | nil => CFail
  | cons l nil => l
  | cons l ls => COr l (CFirst ls)
  end.
Coercion CPatterns : patterns >-> Command.

(** Patterns **)
Inductive RPattern : Type :=
| RIgnore
| RConst
| RHasType (T : Type) (p : RPattern)
| RGet     (idx : nat) (p : RPattern)
| RApp     (f x : RPattern)
| RLam     (t r : RPattern)
| RPi      (t r : RPattern)
| RImpl    (l r : RPattern)
| RExact   {T : Type} (value : T).

(** Actions **)
Definition function  {T} (f : Command T) : Type := T.
Definition id        (T : Type) : Type := T.

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

Set Elimination Schemes.