Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.Member.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.

Set Implicit Arguments.
Set Strict Implicit.

(* This is the universe of the reified language *)
Universe Urefl.

Section simple_dep_types.
  Variable Tsymbol : Type.
  Variable TsymbolD : Tsymbol -> Type@{Urefl}.

  Inductive type : Type :=
  | TArr : type -> type -> type
  | TInj : Tsymbol -> type.

  Fixpoint typeD (t : type) : Type@{Urefl} :=
    match t with
    | TArr a b => typeD a -> typeD b
    | TInj s => TsymbolD s
    end.

  Variable Tsymbol_eq_dec : forall a b : Tsymbol, {a = b} + {a <> b}.

  (** TODO: If we move to a weaker notion of types, e.g. with reduction,
   ** we're going to need a weaker equivalence relation
   **)
  Fixpoint type_eq_dec (t t' : type) : {t = t'} + {t <> t'}.
  refine
    match t as t , t' as t' return {t = t'} + {t <> t'} with
    | TInj a , TInj b => match Tsymbol_eq_dec a b with
                         | left pf => left (f_equal _ pf)
                         | right pf => right _
                         end
    | TArr d c , TArr d' c' => match type_eq_dec d d'
                                   , type_eq_dec c c'
                               with
                               | left pf , left pf' => left _
                               | _ , _ => right _
                               end
    | _ , _ => right _
    end; try congruence.
  Defined.

  Definition codom (t : type) : type :=
    match t with
    | TArr _ c => c
    | _ => t
    end.

  Definition dom (t : type) : type :=
    match t with
    | TArr d _ => d
    | _ => t
    end.

End simple_dep_types.
