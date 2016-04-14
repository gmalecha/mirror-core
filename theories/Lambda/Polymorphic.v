Require Import ExtLib.Data.Vector.

Set Implicit Arguments.
Set Strict Implicit.

Section poly.
  Variable typ : Type.

  Fixpoint polymorphic (n : nat) T : Type :=
    match n with
    | 0 => T
    | S n => typ -> polymorphic n T
    end.

  Fixpoint inst {T} (n : nat)
  : polymorphic n T -> vector typ n -> T :=
    match n as n return polymorphic n T -> vector typ n -> T with
    | 0 => fun p _ => p
    | S n => fun p a => inst (p (Vector.vector_hd a)) (Vector.vector_tl a)
    end.
End poly.

Arguments inst {typ T n} p v : clear implicits, rename.