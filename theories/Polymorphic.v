Require Import ExtLib.Data.Vector.
Require Import ExtLib.Structures.Functor.

Set Implicit Arguments.
Set Strict Implicit.
Set Universe Polymorphism.

Section poly.
  Variable typ : Set.

  Fixpoint polymorphic@{U} (n : nat) (T : Type@{U}) : Type@{U} :=
    match n return Type@{U} with
    | 0 => T
    | S n => typ -> polymorphic n T
    end.

  Section polymorphicD.
    Context {T : Type} (TD : T -> Prop).

    Fixpoint polymorphicD {n} : polymorphic n T -> Prop :=
      match n as n return polymorphic n T -> Prop with
      | 0 => fun p => TD p
      | S n => fun p => forall t, polymorphicD (p t)
      end.
  End polymorphicD.

  Fixpoint inst {T} (n : nat)
  : polymorphic n T -> vector typ n -> T :=
    match n as n return polymorphic n T -> vector typ n -> T with
    | 0 => fun p _ => p
    | S n => fun p a => inst (p (Vector.vector_hd a)) (Vector.vector_tl a)
    end.

  Theorem inst_sound
  : forall {T} {n} (y: polymorphic n T) (P : T -> Prop) v,
      polymorphicD P y ->
      P (inst y v).
  Proof.
    induction n; simpl; eauto.
    intros; eapply IHn; eauto.
  Qed.

  Section make.
    Context {U : Type}.
    Fixpoint make_polymorphic n {struct n}
    : (vector typ n -> U) -> polymorphic n U :=
      match n as n return (vector typ n -> U) -> polymorphic n U with
      | 0 => fun P => P (Vnil _)
      | S n' => fun P => fun v => (make_polymorphic (fun V => P (Vcons v V)))
      end.

    Theorem inst_make_polymorphic
    : forall n f v,
        @inst U n (make_polymorphic f) v = f v.
    Proof.
      induction v; simpl; try rewrite IHv; reflexivity.
    Qed.

    Theorem polymorphicD_make_polymorphic
    : forall (UD : U -> Prop) n (p : vector _ n -> _),
        (forall v, UD (p v)) ->
        polymorphicD UD (make_polymorphic p).
    Proof.
      induction n; simpl; eauto.
    Qed.

  End make.
End poly.

Arguments make_polymorphic {_ _ n} _.
Arguments polymorphicD {_ _} _ {n} _.

Section fmap_polymorphic.
  Context {Z : Set} {T U : Type}.
  Variable f : T -> U.
  Fixpoint fmap_polymorphic (n : nat)
  : polymorphic Z n T -> polymorphic Z n U :=
    match n with
    | 0 => f
    | S n => fun x y => fmap_polymorphic n (x y)
    end.
End fmap_polymorphic.

Instance Functor_polymorphic Z n : Functor (polymorphic Z n) :=
{ fmap := fun T U f => @fmap_polymorphic Z T U f n }.

Arguments inst {typ T n} p v : clear implicits, rename.

Require Import MirrorCore.Reify.ReifyClass.

Section rpolymorphic.
  Context {T : Set} {U : Type}.
  Context {r : Reify U}.

  Fixpoint rpolymorphic n : Command (polymorphic T n U) :=
    match n as n return Command (polymorphic T n U) with
    | 0 => CCall (reify_scheme U)
    | S n => Patterns.CPiMeta (rpolymorphic n)
    end.

  Global Instance Reify_polymorphic n : Reify (polymorphic T n U) :=
  { reify_scheme := CCall (rpolymorphic n) }.
End rpolymorphic.

Arguments rpolymorphic _ _ _ _ : clear implicits.