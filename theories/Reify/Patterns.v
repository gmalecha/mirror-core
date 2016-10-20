Require Coq.FSets.FMapPositive.

Unset Elimination Schemes.
Set Printing Universes.

(* NOTE: These should realy be axioms **)
Inductive table (K : Type) : Type := a_table.
Inductive typed_table (K T : Type) : Type := a_typed_table.
Inductive patterns (T : Type) : Type := a_pattern.

Polymorphic Fixpoint action_pattern@{A} (ls : list Type@{A}) (r : Type@{A}) : Type@{A} :=
  match ls with
  | nil => r
  | Datatypes.cons l ls => l -> action_pattern ls r
  end.

(** Patterns **)
Polymorphic Inductive RPattern@{U} : Prop :=
| RIgnore
| RConst
| RHasType (T : Type@{U}) (p : RPattern)
| RGet     (idx : nat) (p : RPattern)
| RApp     (f x : RPattern)
| RLam     (t r : RPattern)
| RPi      (t r : RPattern)
| RImpl    (l r : RPattern)
| RExact   {T : Type@{U}} (value : T).



Polymorphic Inductive RTemplate@{U} : Type@{U} -> Prop :=
| RRet : forall (T : Type@{U}), T -> RTemplate T
| RDo  : forall (T U : Type@{U}), RAction U -> RTemplate (U -> T) -> RTemplate T
with RAction@{U} : Type@{U} -> Prop :=
| RId : forall (T : Type@{U}), RAction T
| RCmd : forall (T : Type@{U}), Command T -> RAction T
with Command@{U} : Type@{U} -> Prop :=
  (* Structural combinators *)
| CFix        : forall {T : Type@{U}}, Command T -> Command T
| CRec        : forall {T : Type@{U}}, nat -> Command T
| CCall       : forall {T : Type@{U}}, Command T -> Command T
| CMap        : forall {T F : Type@{U}} (f : F -> T) (c : Command F), Command T
| COr         : forall {T : Type@{U}} (a b : Command T), Command T
| CFail       : forall {T : Type@{U}}, Command T
  (* Simple schemes *)
| CApp        : forall {T U V : Type@{U}} (_ : Command T) (_ : Command U)
                       (app : T -> U -> V), Command V
| CAbs        : forall {T U V : Type@{U}} (_ : Command U) (_ : Command V)
                       (lam : U -> V -> T), Command T
| CVar        : forall {T : Type@{U}} (var : nat -> T), Command T
| CPiMeta     : forall {T U : Type@{U}} (a : Command U), Command (T -> U)
  (* Patterns *)
| CPatternTr  : forall {T : Type@{U}}, list (RPattern@{U} * RTemplate T) -> Command T
| CPatterns   : forall {T : Type@{U}} (f : patterns T), Command T
  (* Tables *)
| CTable      : forall {T : Type@{U}} (t : table T), Command T
| CTypedTable : forall {T Ty : Type@{U}} (cTy : Command Ty) (t : typed_table T Ty), Command T.


Polymorphic Definition CPattern T ptr br : Command T :=
  CPatternTr ((ptr, br) :: nil).
Arguments CPattern {_} _ _.

Arguments CPatterns {_} _.
Arguments CApp {_ _ _} _ _ _.
Arguments CAbs {_ _ _} _ _ _.
Arguments CVar {_} _.
Arguments CTable {_} _.
Arguments CTypedTable {_ _} _ _.
Arguments CMap {_ _} _ _.
Arguments CFail {_}.
Arguments COr {_} _ _.
Arguments CPiMeta {_ _} _.
Arguments CPatternTr {T} _.
Arguments CRec {_} _.
Arguments CFix {_} _.

Arguments RRet {_} _.
Arguments RDo {_ _} _ _.
Arguments RId {_}.
Arguments RCmd {_} _.


Polymorphic Fixpoint CFirst_@{U} {T : Type@{U}} (ls : list (Command@{U} T))
: Command@{U} T :=
  match ls with
  | nil => CFail
  | cons l nil => l
  | cons l ls => COr l (CFirst_ ls)
  end.
Notation "'CFirst' ls" :=
  ltac:(let x := eval simpl CFirst_ in (CFirst_ ls%list) in
        exact x) (at level 0).
Coercion CPatterns : patterns >-> Command.


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