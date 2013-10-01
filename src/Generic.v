Require Import List.
Require Import ExtLib.Data.Vector.
Require Import ExtLib.Data.HList.

Set Implicit Arguments.
Set Strict Implicit.

Section quant.
  Variable T : Type.

  Fixpoint quant (n : nat) : Type :=
    match n with
      | 0 => T
      | S n => T -> quant n
    end.

  Fixpoint qapply (n : nat) (ls : list T) : quant n -> option T :=
    match n as n , ls return quant n -> option T with
      | 0 , nil => fun t => Some t
      | S n , l :: ls => fun f => @qapply n ls (f l)
      | _ , _ => fun _ => None
    end.

  Fixpoint qapply_v (n : nat) : vector T n -> quant n -> T :=
    match n as n return vector T n -> quant n -> T with
      | 0 => fun _ x => x
      | S n => fun args x => qapply_v (vector_tl args) (x (vector_hd args))
    end.

  Fixpoint parametric (n : nat) (acc : list T) (k : list T -> Type) : Type :=
    match n with
      | 0 => k acc
      | S n => forall T : T, parametric n (T :: acc) k
    end.

End quant.
