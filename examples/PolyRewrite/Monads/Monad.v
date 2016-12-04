(* A module-based implementation of monads,
   similar to Cancel example's implementation of monoids *)
Require Import ExtLib.Structures.Monad.

Module Type Monad.
  Parameter M : Type -> Type.
  Parameter M_mon : Monad M.

  (* used for demos, to prevent law 1 from getting too much.
     has the same type as Bind but isn't bind.
 *)
  Axiom monad_left_id : forall {A B : Type} (f : A -> M B) (a : A),
      bind (ret a) f = f a.
  Axiom monad_right_id : forall {A : Type} (m : M A),
      bind m ret = m.
  Axiom monad_assoc : forall {A B C : Type} (f : A -> M B) (g : B -> M C) (m : M A),
      bind (bind m f) g = bind m (fun x => bind (f x) g).

End Monad.

Module Type Frob (M : Monad).
  Import M.

  (* if we have time we should polymorphize *)
  Axiom frob : nat -> M nat.
End Frob.