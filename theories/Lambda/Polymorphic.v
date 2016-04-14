Require Import ExtLib.Data.Vector.
Require Import ExtLib.Structures.Functor.

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

Section fmap_polymorphic.
  Context {Z T U : Type}.
  Variable f : T -> U.
  Fixpoint fmap_polymorphic (n : nat)
  : polymorphic Z n T -> polymorphic Z n U :=
    match n with
    | 0 => f
    | S n => fun x y => fmap_polymorphic n (x y)
    end.
End fmap_polymorphic.

Instance Functor_polymorphic Z n : Functor (polymorphic Z n) :=
{ fmap := fun T U f => @fmap_polymorphic Z T U f n }.

Arguments inst {typ T n} p v : clear implicits, rename.