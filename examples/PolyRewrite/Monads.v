(**
   Monad rewriter example
   Builds on ext-lib monads.
 *)

Require Import ExtLib.Structures.Monad.
Require Import McExamples.PolyRewrite.MSimpleMonads.
Require Import McExamples.PolyRewrite.MSimpleMonadsReify.

Section MonadLaws.

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

Section MonadRewrite.
  Variable M : Type -> Type.
  Variable M_mon : Monad M.
  Variable M_monOk : MonadLaws M M_mon.

  (* Set-up for Ltac-based rewriter *)
  Definition lem1 := @monad_left_id M M_mon M_monOk.
  Definition lem2 := @monad_right_id M M_mon M_monOk.
  Definition lem3 := @monad_assoc M M_mon M_monOk.

  Create HintDb monads.

  Hint Rewrite lem1 lem2 lem3 : monads.

  Definition ex1 := @bind M M_mon _ _ (ret 5) (fun x => ret (x + 1))%nat.
  (* tests *)
  Goal exists x, ex1 = x.
  Proof.
    unfold ex1.
    autorewrite with monads.
  Abort.

  (* TODO: Applicative and stuff *)
  Fixpoint makeLeftIdTest (n : nat) : M nat :=
    match n with
    | O => ret 1
    | S n' => bind (makeLeftIdTest n') (fun x => ret (x + 1))
    end.

  Goal (exists x, makeLeftIdTest 80 = x).
    compute.
    Time autorewrite with monads. (* 2.293s for n = 80 *)
  Abort.

  Fixpoint makeRightIdTest (n : nat) : M nat :=
    match n with
    | O => ret 1
    | S n' => bind (makeRightIdTest n') ret
    end.

  Goal (exists x, makeRightIdTest 80 = x).
    compute.
    Time autorewrite with monads. (* 1.454s for n = 80 *)
  Abort.

  Section AssocTest.

    Variable frob : forall x, x -> M x.

    Fixpoint makeAssocTest (n : nat) : M nat :=
      match n with
      | 0 => @frob nat 1
      | S n' => bind (makeAssocTest n') (fun x => ret (x + 1))
      end.

    Require Import Coq.Classes.Morphisms.
    Require Import Coq.Logic.FunctionalExtensionality.

    (* Needed to setoid_rewrite monadic expressions *)
    Instance bind_proper :
      forall T U,
        Proper (@eq (M T) ==> pointwise_relation T (@eq (M U)) ==> @eq (M U)) bind.
          intros. red. red. intros; subst.
          red. intros.
          unfold pointwise_relation in H.
          apply functional_extensionality in H.
          subst.
          reflexivity.
    Qed.

          (* change to repeat first *)
          (* rtac - reify lemmas, write automation
             will need a simple-ish monad language with bind and ret
             use funext for now
            *)
    Goal (exists x, makeAssocTest 10 = x).
    Proof.
      simpl.
      Time (repeat (first [setoid_rewrite lem1
                          |setoid_rewrite lem2
                          |setoid_rewrite lem3]
           )).
    Abort.

    (*   n = depth of overall tree
         k = depth of associations at each node *)
    Fixpoint makeLeftIdAssocTest (n : nat) (k : nat) : M nat :=
      match n with
      | 0 => @frob nat 1
      | S n' => @bind M _ _ nat (makeLeftIdAssocTest n' k) (fun _ => makeAssocTest k)
      end.

    (* 2 2 is another common test *)
    Goal (exists x, makeLeftIdAssocTest 2 2 = x).
      simpl.
(*      repeat setoid_rewrite lem3.
      setoid_rewrite lem1. *)
      
      Time (repeat (first [setoid_rewrite lem1
                          |setoid_rewrite lem2
                          |setoid_rewrite lem3]
           )). (*14.111s for n=8, k=5 *)
    Abort.

    Goal (exists x, makeLeftIdAssocTest 8 5 = x).
      simpl.
      
      Time (repeat (first [setoid_rewrite lem1
                          |setoid_rewrite lem2
                          |setoid_rewrite lem3]
           )). (*14.111s for n=8, k=5 *)
    Abort.


    (* n = depth *)
    Fixpoint makeRightIdAssocTest (n : nat) : M nat :=
      match n with
      | 0 => @bind M _ _ nat (@frob nat 1) ret
      | S n' => bind (makeRightIdAssocTest n') (fun k => frob nat (k + 1))
      end.

    Goal (exists x, makeRightIdAssocTest 20 = x).
    Proof.
      simpl.
      Time (repeat (first [setoid_rewrite lem1
                          |setoid_rewrite lem2
                          |setoid_rewrite lem3]
           )). (*2.366s for k=20 *)
    Abort.

  End AssocTest.
 
End MonadRewrite.
  

