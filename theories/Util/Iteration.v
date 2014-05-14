Require Import Coq.Lists.List.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.Injection.

Set Implicit Arguments.
Set Strict Implicit.

Section iteration.
  Context (T U : Type) (f : T -> option U).

  Fixpoint first_success  (ls : list T) : option U :=
    match ls with
      | nil => None
      | l :: ls =>
        match f l with
          | None => first_success ls
          | x => x
        end
    end.

  Lemma first_success_sound
  : forall ls val,
      first_success ls = Some val ->
      exists l,
        In l ls /\ f l = Some val.
  Proof.
    induction ls; simpl; intros.
    - congruence.
    - consider (f a); intros.
      + exists a. inv_all; subst. auto.
      + apply IHls in H0. destruct H0. intuition. eauto.
  Qed.

  Variable (f' : T -> U -> option U).

  Fixpoint all_success (ls : list T) (acc : U)
  : option U :=
    match ls with
      | nil => Some acc
      | l :: ls =>
        match f' l acc with
          | None => None
          | Some x => all_success ls x
        end
    end.

End iteration.
