(**
   Monad rewriter example
   Builds on ext-lib monads.
 *)

Require Import ExtLib.Structures.Monad.

Section MonadLaws.

  Print Monad.

  Variable M : Type -> Type.
  Variable M_mon : Monad M.

  (* Monad Laws *)
  Class MonadLaws : Type :=
    { monad_left_id : forall {A B : Type} (f : A -> M B) (a : A),
        bind (ret a) f = f a;
      monad_right_id : forall {A : Type} (m : M A),
          bind m ret = m;
      monad_assoc : forall {A B C : Type} (f : A -> M B) (g : B -> M C) (m : M A),
        bind (bind m f) g = bind m (fun x => bind (f x) g)
    }.
End MonadLaws.

Section Option.
  Require Import ExtLib.Data.Monads.OptionMonad.
  Instance OptionMonadOk : MonadLaws option Monad_option.
  Proof.
    constructor.
    { simpl; auto. }
    { intros. destruct m; reflexivity. }
    { intros.
      destruct m.
      { simpl. destruct (f a); reflexivity. }
      { simpl. reflexivity. } }
  Qed.
End Option.
  
  (* From MonadLaws.v *)
  (*
  Class MonadLaws : Type :=
  { bind_of_return : forall {A B : Type@{d}} (eA : type A) (eB : type B),
    typeOk eA -> typeOk eB ->
    forall (a:A) (f:A -> m B),
    proper a -> proper f ->
    equal (bind (ret a) f) (f a)
  ; return_of_bind : forall {A : Type@{d}} (eA : type A),
    typeOk eA ->
    forall (aM:m A) (f:A -> m A),
    (forall x, equal (f x) (ret x)) ->
    proper aM ->
    equal (bind aM f) aM
  ; bind_associativity :
    forall {A B C : Type@{d}} (eA : type A) (eB : type B) (eC : type C),
      typeOk eA -> typeOk eB -> typeOk eC ->
      forall (aM:m A) (f:A -> m B) (g:B -> m C),
      proper aM ->
      proper f ->
      proper g ->
      equal (bind (bind aM f) g) (bind aM (fun a => bind (f a) g))
  ; ret_proper :> forall {A:Type@{d}} (eA : type A), typeOk eA ->
    proper ret
  ; bind_proper :> forall {A B:Type@{d}} (eA : type A) (eB : type B),
    typeOk eA -> typeOk eB ->
    proper (@bind m _ A B)
  }.

*)

End Monad.