(**
   Monad rewriter example
   Builds on ext-lib monads.
 *)

(*Require Import McExamples.PolyRewrite.Monads.MSimpleMonads.
Require Import McExamples.PolyRewrite.Monads.MSimpleMonadsReify.*)
Require Import McExamples.PolyRewrite.Monads.Monad.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Tactics.

Module TheMonad (M : Monad) (F : Frob M).
  Import M.
  Import F.

  (* Set-up for Ltac-based rewriter *)

  Definition lem1 := @monad_left_id.
  (* M M_mon M_monOk. *)
  Definition lem2 := @monad_right_id.
  Definition lem3 := @monad_assoc.

  Create HintDb monads.

  Hint Rewrite lem1 lem2 lem3 : monads.

  Definition ex1 := @bind M M_mon _ _ (ret 5) (fun x => ret (x + 1))%nat.
  (* tests *)
  Goal exists x, ex1 = x.
  Proof.
    unfold ex1.
    Time rewrite_strat (bottomup (hints monads; eval cbv beta)).
    eexists; reflexivity.
  Qed.

  (* TODO: Applicative and stuff *)
  Fixpoint makeLeftIdTest (n : nat) : M nat :=
    match n with
    | O => ret 1
    | S n' => bind (makeLeftIdTest n') (fun x => ret (x + 1))
    end.

  Goal (exists x, makeLeftIdTest 80 = x).
    cbv beta zeta iota delta -[bind ret].
    (*    Time autorewrite with monads. *)
    Time  rewrite_strat (bottomup (hints monads; eval cbv beta)).
    eexists; reflexivity.
  Qed.

  Fixpoint makeRightIdTest (n : nat) : M nat :=
    match n with
    | O => ret 1
    | S n' => bind (makeRightIdTest n') ret
    end.

  Goal (exists x, makeRightIdTest 80 = x).
    compute.
    Time autorewrite with monads. (* 1.454s for n = 80 *)
    eexists; reflexivity.
  Qed.

  Fixpoint makeAssocTest (n : nat) : M nat :=
    match n with
    | 0 => frob 1
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
    Time (rewrite_strat (bottomup (hints monads; eval cbv beta))).
    eexists; reflexivity.
  Qed.

  (*   n = depth of overall tree
         k = depth of associations at each node *)
  Fixpoint makeLeftIdAssocTest (n : nat) (k : nat) : M nat :=
    match n with
    | 0 => frob 1
    | S n' => @bind M _ _ nat (makeLeftIdAssocTest n' k) (fun _ => makeAssocTest k)
    end.

  (* 2 2 is another common test *)
  Goal (exists x, makeLeftIdAssocTest 2 2 = x).
    simpl.
    Time rewrite_strat (bottomup (hints monads; eval cbv beta)).
    eexists; reflexivity.
  Qed.
  
  Goal (exists x, makeLeftIdAssocTest 8 5 = x).
    simpl.
    (* i don't understand why we must have this outer repeat... *)
    Time (rewrite_strat ((bottomup (hints monads; eval cbv beta)))).
    eexists; reflexivity.
  Qed.

  (* n = depth *)
  Fixpoint makeRightIdAssocTest (n : nat) : M nat :=
    match n with
    | 0 => @bind M _ _ nat (frob 1) ret
    | S n' => bind (makeRightIdAssocTest n') (fun k => frob (k + 1))
    end.

  Goal (exists x, makeRightIdAssocTest 25 = x).
  Proof.
    simpl.
    Time rewrite_strat (bottomup (hints monads; eval cbv beta)).
    eexists; reflexivity.
  Qed.

  Module Demo.
    Definition goal := fun n => (exists x, makeRightIdAssocTest n = x).
    Ltac prep := unfold goal; simpl.
    Ltac run := rewrite_strat (bottomup (hints monads; eval cbv beta)).
    Ltac cleanup := eexists; reflexivity.
  End Demo.

End TheMonad.


