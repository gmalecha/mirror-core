Require Import Coq.Relations.Relations.
Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.List.
Require Import MirrorCore.EnvI.

Set Implicit Arguments.
Set Strict Implicit.

Section OpenT.
  Variable typ : Type.
  Variable typD : typ -> Type.
  Variables tvs : tenv typ.

  Definition OpenT (T : Type) :=
    hlist typD tvs -> T.

  Global Instance Applicative_OpenT : Applicative OpenT :=
  { pure := fun _ val _ => val
  ; ap := fun _ _ f x vs => (f vs) (x vs)
  }.

  Global Instance Functor_OpenT : Functor  OpenT :=
  { fmap := fun _ _ f x => fun vs => (f (x vs)) }.

  Definition OpenT_Use (n : nat) : option { t : typ & OpenT (typD t) } :=
    match nth_error_get_hlist_nth _ tvs n with
      | None => None
      | Some (existT t get) =>
        Some (@existT _ (fun t => OpenT (typD t)) t get)
    end.

  Section OpenTrel.
    Variable Rd : forall t, relation (typD t).
    Context {T : Type}.
    Variable R : relation T.

    (** TODO: Move to Data.HList **)
    Theorem Symmetric_equiv_hlist
    : (forall t, Symmetric (@Rd t)) ->
      forall ls, Symmetric (@equiv_hlist _ _ Rd ls).
    Proof.
      compute.
      induction 2. constructor. constructor. apply H; auto. auto.
    Qed.


    Definition OpenTrel : relation (OpenT T) :=
      fun a b => forall x y, equiv_hlist Rd x y -> R (a x) (b y).

    Theorem Symmetric_OpenTrel
    : (forall t, Symmetric (@Rd t)) -> Symmetric R -> Symmetric OpenTrel.
    Proof.
      compute. intros. apply H0. apply H1.
      eapply Symmetric_equiv_hlist; eauto.
    Qed.

    Theorem Transitive_OpenTrel
    : (forall t, Reflexive (@Rd t)) -> Transitive R -> Transitive OpenTrel.
    Proof.
      compute. intros.
      eapply H0.  eapply H1. eassumption.
      eapply H2. eapply Reflexive_equiv_hlist. eauto.
    Qed.
  End OpenTrel.

  Section OpenTeq.
    Context {T : Type}.
    Variable R : relation T.

    Definition OpenTeq : relation (OpenT T) :=
      OpenTrel (fun x => @eq _) R.

    Theorem Reflexive_OpenTeq : Reflexive R -> Reflexive OpenTeq.
    Proof.
      compute. intros. eapply equiv_eq_eq in H0. subst.
      apply H.
    Qed.

    Theorem Symmetric_OpenTeq : Symmetric R -> Symmetric OpenTeq.
    Proof.
      compute. intros. apply H. apply H0.
      symmetry. assumption.
    Qed.

    Theorem Transitive_OpenTeq : Transitive R -> Transitive OpenTeq.
    Proof.
      compute. intros. eapply H. eapply H0; try eassumption.
      eapply H1. reflexivity.
    Qed.
  End OpenTeq.


  Theorem pure_eq
  : forall T (R : relation T) a b, R a b -> OpenTeq R (pure a) (pure b).
  Proof. compute; intros; assumption. Qed.

  Theorem ap_eq
  : forall T U (Rt : relation T) (Ru : relation U) f g a b,
      OpenTeq (Rt ==> Ru)%signature f g -> OpenTeq Rt a b ->
      OpenTeq Ru (ap f a) (ap g b).
  Proof. compute. auto. Qed.

  Theorem fmap_eq
  : forall T U (Rt : relation T) (Ru : relation U) f g a b,
      (Rt ==> Ru)%signature f g -> OpenTeq Rt a b ->
      OpenTeq Ru (fmap f a) (fmap g b).
  Proof. compute; auto. Qed.

  Theorem eq_OpenT_eq
  : forall T F (a b : T) (pf : a = b) val,
      match pf in _ = x return OpenT (F x) with
        | eq_refl => val
      end =
      fmap (fun v : F a =>
              match pf in _ = x return F x with
                | eq_refl => v
              end) val.
  Proof.
    destruct pf. reflexivity.
  Qed.

End OpenT.

Section OpenT_Abs.
  Variable typ : Type.
  Variable typD : typ -> Type.

  Definition Open_Abs {tvs t T} (f : OpenT typD (t :: tvs) T)
  : OpenT typD tvs (typD t -> T) :=
    fun vs x => f (Hcons x vs).

  Definition Open_App {tvs T U} (f : OpenT typD tvs (T -> U))
             (x : OpenT typD tvs T)
  : OpenT typD tvs U :=
    fun vs => (f vs) (x vs).
End OpenT_Abs.

Hint Rewrite eq_OpenT_eq : eq_rw.