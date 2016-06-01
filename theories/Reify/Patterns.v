Require Coq.FSets.FMapPositive.

Unset Elimination Schemes.

(* NOTE: These should realy be axioms **)
Inductive table (K : Type) : Type := a_table.
Inductive typed_table (K T : Type) : Type := a_typed_table.
Inductive patterns (T : Type) : Type := a_pattern.

Fixpoint action_pattern (ls : list Type) (r : Type) : Type :=
  match ls with
  | nil => r
  | List.cons l ls => l -> action_pattern ls r
  end.

(** Patterns **)
Inductive RPattern : Prop :=
| RIgnore
| RConst
| RHasType (T : Type) (p : RPattern)
| RGet     (idx : nat) (p : RPattern)
| RApp     (f x : RPattern)
| RLam     (t r : RPattern)
| RPi      (t r : RPattern)
| RImpl    (l r : RPattern)
| RExact   {T : Type} (value : T).

Record RBranch (T : Type) : Prop := mkRBranch
{ rcaptures : list Type
; rpattern  : RPattern
; rtemplate : action_pattern rcaptures T
}.

(** Commands **)
(* Command T parses a constr into a T *)
Inductive Command : Type -> Prop :=
  (* Structural combinators *)
| CFix        : forall {T}, Command T -> Command T
| CRec        : forall {T}, nat -> Command T
| CCall       : forall {T}, Command T -> Command T
| CMap        : forall {T F : Type} (f : F -> T) (c : Command F), Command T
| COr         : forall {T} (a b : Command T), Command T
| CFail       : forall {T}, Command T
  (* Simple schemes *)
| CApp        : forall {T U V} (_ : Command T) (_ : Command U)
                       (app : T -> U -> V), Command V
| CAbs        : forall {T U V : Type} (_ : Command U) (_ : Command V)
                       (lam : U -> V -> T), Command T
| CVar        : forall {T} (var : nat -> T), Command T
| CPiMeta     : forall {T U} (a : Command U), Command (T -> U)
  (* Patterns *)
| CPatternTr  : forall {T}, list (RBranch T) -> Command T
| CPatterns   : forall {T} (f : patterns T), Command T
  (* Tables *)
| CTable      : forall {T} (t : table T), Command T
| CTypedTable : forall {T Ty : Type} (cTy : Command Ty) (t : typed_table T Ty), Command T.

(*
Notation "'CApp_' x" := (@CApp _ _ _ (CRec 0) (CRec 0) x) (at level 0).
(*
Definition CApp_ {T} (f : T -> T -> T) : Command T :=
  @CApp T T T (CRec 0) (CRec 0) f.
*)
Notation "'CAbs_' c x"
Definition CAbs_ {T Ty} (c : Command Ty) (f : Ty -> T -> T) : Command T :=
  @CAbs T Ty T c (CRec 0) f.
*)
Definition CPattern T ls ptr br : Command T :=
  CPatternTr (mkRBranch T ls ptr br :: nil).
Arguments CPattern {_} [_] _ _.


(** Actions **)
Definition function  {T} (f : Command T) : Type := T.
Definition id        (T : Type) : Type := T.

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

Fixpoint CFirst_ {T} (ls : list (Command T)) : Command T :=
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