Require Import Coq.omega.Omega.
Require Import ExtLib.Data.PList.
Require Import ExtLib.Data.POption.
Require Import MirrorCore.ModularTypes.

Set Implicit Arguments.
Set Strict Implicit.
Set Universe Polymorphism.
Set Primitive Projections.

(** TODO(gmalecha): This should go somewhere else **)
Definition nat_get_eq (n m : nat) (pf : unit -> n = m) : n = m :=
  match PeanoNat.Nat.eq_dec n m with
  | left pf => pf
  | right bad => match bad (pf tt) with end
  end.

(** TODO(gmalecha): This should go in ExtLib.Data.PList **)
Section pnth_error.
  Context {T : Type}.
  Fixpoint pnth_error (ls : plist T) (n : nat) : poption T :=
    match n , ls with
    | 0 , pcons l _ => pSome l
    | S n , pcons _ ls => pnth_error ls n
    | _ , _ => pNone
    end.
End pnth_error.


(** TODO(gmalecha): This should become a functor to avoid the extra
 ** parameter everywhere
 **)
Section dlist.
  Variable (F : nat -> Type).

  Inductive dlist (n : nat) : Type :=
  | dnil : dlist n
  | dcons : F n -> dlist (S n) -> dlist n.

  Fixpoint plus_k a b : nat :=
    match a with
    | 0 => b
    | S n => plus_k n (S b)
    end.

  Fixpoint dlist_get {n} m (dl : dlist n) : poption (F (plus_k m n)) :=
    match dl with
    | dnil _ => pNone
    | @dcons _ f dl0 =>
      match m as n1 return poption (F (plus_k n1 n)) with
      | 0 => pSome f
      | S m0 => dlist_get m0 dl0
      end
    end.

  Theorem plus_k_conv : forall m n, plus_k m n = m + n.
  Proof.
    induction m.
    - reflexivity.
    - simpl; intros.
      rewrite IHm.
      omega.
  Qed.

  Definition get_env n m (dl : dlist m)
  : poption (F (m + n)).
    rewrite PeanoNat.Nat.add_comm.
    rewrite <- plus_k_conv.
    eapply dlist_get. assumption.
  Defined.

  Definition dlist_empty := dnil.

  Lemma plus_0 : forall n, n = n + 0.
  Proof.
    induction n; simpl; auto.
  Defined.

  Definition dlist_tl {n} (dl : dlist n) : dlist (S n) :=
    match dl with
    | dnil _ => dnil _
    | dcons _ dl => dl
    end.

  Section insert.
    Variable (default : forall n, F n).

    Fixpoint dlist_insert n m (f : F (m + n) -> F (m + n)) {struct n}
      : dlist m -> dlist m.
      destruct n.
      - destruct 1.
        + apply dcons. rewrite <- plus_0 in f. apply f. apply default.
          apply dnil.
        + apply dcons. rewrite <- plus_0 in f. apply f. apply f0. apply dnil.
      - intros.
        apply dcons.
        + destruct X.
          * apply default.
          * apply f0.
        + rewrite PeanoNat.Nat.add_comm in f.  simpl in *.
          rewrite PeanoNat.Nat.add_comm in f.
          eapply dlist_insert. eapply f.
          apply dlist_tl. apply X.
    Defined.
  End insert.

End dlist.

Section symD.
  (** TODO(gmalecha): The contents should use positives rather than nats *)
  Variable env : dlist (fun n => plist (type_for_arity n)) 0.

  Record sym (n : nat) : Type :=
  { idx : nat
  ; _ : match get_env n env with
        | pNone => False
        | pSome x => match pnth_error x idx with
                     | pNone => False
                     | pSome _ => True
                     end
        end }.

  Fixpoint symD {n : nat} (s : sym n) : type_for_arity n.
    destruct s.
    destruct (get_env n env).
    destruct (pnth_error p idx0).
    apply t.
    exfalso. assumption.
    exfalso. assumption.
  Defined.
End symD.

Definition types : Type := plist (sigT type_for_arity).
Definition a_type := @existT _ type_for_arity.

Fixpoint build_env (t : types) : dlist (fun n => plist (type_for_arity n)) 0.
  destruct t.
  - apply dnil.
  - eapply dlist_insert.
    * intros. apply pnil.
    * instantiate (1:= projT1 s).
      exact (pcons (projT2 s)).
    * apply (build_env t). 
Defined.

(** * Demo **)
Definition test : types :=
  pcons (a_type 0 nat)
        (pcons (a_type 1 list)
               (pcons (a_type 0 bool)
               pnil)).

Eval cbv beta iota zeta delta - [ type_for_arity ] in build_env test.