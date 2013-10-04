Require Import RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.Consider.

Set Implicit Arguments.
Set Strict Implicit.

Section logic.
  Variable P : Type.

  Class Logic : Type :=
  { (** Entails P Q ==> P |- Q **)
    Entails : P -> P -> Prop
  ; Tr : P
  ; Fa : P
  ; And : P -> P -> P
  ; Or : P -> P -> P
  ; Impl : P -> P -> P
  }.

  Variable Logic_P : Logic.

  Class LogicLaws : Type :=
  { Entails_refl :> Reflexive Entails
  ; Entails_trans :> Transitive Entails
  ; Tr_True : forall G, Entails G Tr
  ; Fa_False : forall G, Entails Fa G

  ; ImplI : forall G P Q, Entails (And P G) Q -> Entails G (Impl P Q)
  ; ImplE : forall P Q, Entails (And (Impl P Q) P) Q

  ; AndI : forall G P Q, Entails G P -> Entails G Q -> Entails G (And P Q)
  ; AndEL : forall P Q R, Entails P R -> Entails (And P Q) R
  ; AndER : forall P Q R, Entails Q R -> Entails (And P Q) R

  ; OrIL : forall G P Q, Entails G P -> Entails G (Or P Q)
  ; OrIR : forall G P Q, Entails G Q -> Entails G (Or P Q)
  ; OrE : forall P Q R, Entails P R -> Entails Q R -> Entails (Or P Q) R
  }.

  Variable LogicLaws_P : LogicLaws.

  Fixpoint Impls (ps : list P) (p : P) : P :=
    match ps with
      | nil => p
      | p' :: ps => Impl p' (Impls ps p)
    end.

  Fixpoint Ands (ps : list P) : P :=
    match ps with
      | nil => Tr
      | p :: ps => And p (Ands ps)
    end.

  Fixpoint Ors (ps : list P) : P :=
    match ps with
      | nil => Fa
      | p :: ps => Or p (Ands ps)
    end.

  Definition Eq (a b : P) : P :=
    And (Impl a b) (Impl b a).

  Theorem Entails_And_comm_L : forall P Q R,
                                 Entails (And P Q) R ->
                                 Entails (And Q P) R.
  Proof.
    intros. etransitivity. 2: eassumption.
    eapply AndI. eapply AndER. reflexivity.
    eapply AndEL. reflexivity.
  Qed.

  Theorem Entails_And_comm_R : forall P Q R,
                                 Entails R (And P Q) ->
                                 Entails R (And Q P).
  Proof.
    intros. etransitivity. eassumption.
    eapply AndI. eapply AndER. reflexivity.
    eapply AndEL. reflexivity.
  Qed.


  Class Quant : Type :=
  { All : forall (T : Type), (T -> P) -> P
  ; Ex  : forall (T : Type), (T -> P) -> P
  }.

  Class QuantLaws (Q : Quant) : Type :=
  { AllI : forall T G (Pr : T -> P), Entails G (All Pr) -> forall x, Entails G (Pr x)
  ; AllE : forall T G (Pr : T -> P), (forall x, Entails G (Pr x)) -> Entails G (All Pr)
  ; ExI : forall T G (Pr : T -> P) x, Entails G (Ex Pr) -> Entails G (Pr x)
  ; ExE : forall T G (Pr : T -> P), (forall x, Entails (Pr x) G) -> Entails (Ex Pr) G
  }.

End logic.

Hint Resolve Tr_True Fa_False ImplI ImplE AndI AndEL AndER OrIL OrIR OrE : logic.
