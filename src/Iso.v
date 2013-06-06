Require Import ExtLib.Structures.Functor.

Set Implicit Arguments.
Set Strict Implicit.

Section Iso.
  Variable A B : Type.

  Class Iso : Type := mkIso 
  { into : A -> B
  ; outof : B -> A
  }.

  Class IsoOk (iso : Iso) : Type :=
  { into_outof : forall x, into (outof x) = x
  ; outof_into : forall x, outof (into x) = x
  }.

  Class StrongIso : Type :=
  { sinto : forall (F : Type -> Type), F A -> F B
  ; soutof : forall (F : Type -> Type), F B -> F A
  }.

  Definition DistFunc {A B} (f : forall F, F A -> F B) : Prop :=
    forall (F : Type -> Type) (func : Functor F) (fOk : FunctorOk func),
      fmap (@f (fun x => x)) = f _.

  Class StrongIsoOk (SI : StrongIso) : Type :=
  { sinto_dist : DistFunc sinto
  ; soutof_dist : DistFunc soutof
  }.
End Iso.
