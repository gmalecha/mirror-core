Require Import ExtLib.Data.Positive.
Require Import ExtLib.Data.PList.
Require Import ExtLib.Data.Eq.UIP_trans.
Require Import ExtLib.Data.POption.
Require Import ExtLib.Tactics.

Require Import MirrorCore.Util.Compat.

Set Universe Polymorphism.
Set Implicit Arguments.
Set Strict Implicit.

Section OneOfType.

  Universe Uval.
  Variable T : Type@{Uval}.

  Inductive pmap : Type@{Uval} :=
  | Empty : pmap
  | Branch : poption@{Uval} T -> pmap -> pmap -> pmap.
  Arguments Empty.
  Arguments Branch _ _ _.

  Definition pmap_here (p : pmap) : poption@{Uval} T :=
    match p with
    | Empty => pNone
    | Branch d _ _ => d
    end.
  Definition pmap_left (p : pmap) : pmap :=
    match p with
    | Empty => Empty
    | Branch _ l _ => l
    end.
  Definition pmap_right (p : pmap) : pmap :=
    match p with
    | Empty => Empty
    | Branch _ _ r => r
    end.

  Fixpoint pmap_lookup (ts : pmap) (p : positive) : poption@{Uval} T :=
    match p with
    | xH => pmap_here ts
    | xI p => pmap_lookup (pmap_right ts) p
    | xO p => pmap_lookup (pmap_left ts) p
    end.

  Fixpoint pmap_insert (p : positive) (ts : pmap) (x : T) : pmap :=
    match p with
    | xH => Branch (pSome@{Uval} x) (pmap_left ts) (pmap_right ts)
    | xO p => Branch (pmap_here ts)
                     (pmap_insert p (pmap_left ts) x)
                     (pmap_right ts)
    | xI p => Branch (pmap_here ts)
                     (pmap_left ts)
                     (pmap_insert p (pmap_right ts) x)
    end.

  Definition pmap_empty : pmap := Empty.

End OneOfType.

Section pmap_map.
  Universe U1 U2.
  Variable T : Type@{U1}.
  Variable U : Type@{U2}.
  Variable f : T -> U.

  Fixpoint pmap_map (m : pmap T) : pmap U :=
    match m with
    | @Empty _ => @Empty _
    | Branch a b c => Branch match a with
                            | pSome x => pSome (f x)
                            | pNone => pNone
                            end (pmap_map b) (pmap_map c)
    end.

  (** TODO(gmalecha): Theorems *)
End pmap_map.