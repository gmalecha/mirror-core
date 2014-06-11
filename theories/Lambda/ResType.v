Require Import Coq.Relations.Relations.
Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Structures.Monad.
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
  Variables tus tvs : tenv typ.

  Definition OpenT (T : Type) :=
    hlist typD tus -> hlist typD tvs -> T.

  Global Instance Applicative_OpenT : Applicative OpenT :=
  { pure := fun _ val _ _ => val
  ; ap := fun _ _ f x us vs => (f us vs) (x us vs)
  }.

  Global Instance Functor_OpenT : Functor  OpenT :=
  { fmap := fun _ _ f x => fun us vs => (f (x us vs)) }.

  Definition Open_UseU (n : nat) : option { t : typ & OpenT (typD t) } :=
    match nth_error_get_hlist_nth _ tus n with
      | None => None
      | Some (existT t get) =>
        Some (@existT _ (fun t => OpenT (typD t)) t (fun us _ => get us))
    end.

  Definition Open_UseV (n : nat) : option { t : typ & OpenT (typD t) } :=
    match nth_error_get_hlist_nth _ tvs n with
      | None => None
      | Some (existT t get) =>
        Some (@existT _ (fun t => OpenT (typD t)) t (fun _ => get))
    end.

  Definition OpenTeq T (R : relation T) : relation (OpenT T) :=
    fun a b => forall x y, R (a x y) (b x y).

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

End OpenT.

Section OpenT_Abs.
  Variable typ : Type.
  Variable typD : typ -> Type.

  Definition Open_Abs {tus tvs t T} (f : OpenT typD tus (t :: tvs) T)
  : OpenT typD tus tvs (typD t -> T) :=
    fun us vs x => f us (Hcons x vs).
End OpenT_Abs.
