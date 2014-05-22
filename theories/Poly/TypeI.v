Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Data.HList.

Set Implicit Arguments.
Set Strict Implicit.

Set Printing Universes.

Fixpoint nat_eq (a b : nat) {struct a} : option (a = b) :=
  match a as a , b as b return option (a = b) with
    | 0 , 0 => Some eq_refl
    | S a , S b => match nat_eq a b with
                     | Some pf =>
                       Some match pf in _ = t return S a = S t with
                              | eq_refl => eq_refl
                            end
                     | None => None
                   end
    | _ , _ => None
  end.
