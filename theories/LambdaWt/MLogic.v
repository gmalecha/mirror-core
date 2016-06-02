Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Functor.

Set Implicit Arguments.
Set Strict Implicit.
Set Universe Polymorphism.
Set Primitive Projections.

Section MLogic.
  Variable m : Type -> Type.
  Context {Monad_m : Monad m}.
  Context {MonadPlus_m : MonadPlus m}.
  Context {MonadZero_m : MonadZero m}.
  Context {Functor_m : Functor m}.

  Class FLogic : Type :=
  { fmodels : forall {T : Type} (TD : T -> Prop), m T -> Prop
  ; fmodels_fmap : forall T U (f : T -> U) (P Q : _ -> Prop) x,
      (forall x, Q x -> P (f x)) ->
      fmodels Q x ->
      fmodels P (fmap f x) }.

  Class MLogic (f : FLogic) : Type :=
  { fmodels_bind : forall T U (P : T -> Prop) (Q : U -> Prop) c k,
      fmodels P c ->
      (forall x, P x -> fmodels Q (k x)) ->
      fmodels Q (bind c k)
  ; fmodels_ret : forall T (P : T -> Prop) x,
      P x -> fmodels P (ret x)
  ; fmodels_conseq : forall T (P Q : T -> Prop) x,
      (forall x, Q x -> P x) ->
      fmodels Q x ->
      fmodels P x
  }.

  Class MLogicZero (FL : FLogic) : Type :=
  { fmodels_mzero : forall T (P : T -> _), fmodels P mzero }.

  Class MLogicPlus (FL : FLogic) : Type :=
  { fmodels_mplus : forall T U (P : T -> Prop) (Q : U -> Prop)
                           (x : m T) (y : m U),
      fmodels P x ->
      fmodels Q y ->
      fmodels (fun x => match x with
                        | inl x => P x
                        | inr x => Q x
                        end) (mplus x y) }.

  Theorem fmodels_mjoin (FL : FLogic) (ML : MLogic FL) (PL : MLogicPlus FL)
  : forall T (P : T -> Prop) x y,
      fmodels P x ->
      fmodels P y ->
      fmodels P (mjoin x y).
  Proof.
    unfold mjoin.
    intros. eapply fmodels_bind. eapply fmodels_mplus.
    eassumption. eassumption.
    simpl. destruct x0; eauto using fmodels_ret.
  Qed.

End MLogic.
Arguments FLogic _ {_} : clear implicits.
Arguments MLogic _ {_ _ _} : clear implicits.
Arguments MLogicZero _ {_ _ _} : clear implicits.
Arguments MLogicPlus _ {_ _ _} : clear implicits.

Arguments fmodels_mzero {_ _ _ _ _ _} _.
Arguments fmodels_conseq {_ _ _ _ _} _ _ _ _ _ _.
Arguments fmodels_bind {_ _ _ _ _} _ _ _ _ _ _ _ _.
Arguments fmodels_ret {_ _ _ _ _} _ _ _ _.
Arguments fmodels_mplus {_ _ _ _ _} _ _ _ _ _ _ _ _.
Arguments fmodels_fmap {_ _ _ _ _} _ _ _ _ _ _.
Arguments fmodels_mjoin {_ _ _ _ _ _ _} _ _ _ _ _ _.
Arguments fmodels {_ _ _} [T] TD _.

Require Import ExtLib.Data.Monads.IdentityMonad.

Section logic_ident.

  Global Instance FLogic_ident : FLogic ident :=
  { fmodels := fun T P x => P x.(unIdent)
  }.
  Proof.
    destruct x; simpl. auto.
  Defined.

  Global Instance MLogic_ident : MLogic ident.
  Proof.
    constructor.
    { destruct c. simpl; eauto. }
    { auto. }
    { destruct x; simpl; eauto. }
  Defined.

End logic_ident.

Require Import ExtLib.Data.Monads.OptionMonad.

Section logic_option.
  Global Instance FLogic_option : FLogic option :=
  { fmodels := fun T P x => match x with
                            | None => True
                            | Some x => P x
                            end }.
  Proof.
    destruct x; simpl; auto.
  Defined.

  Global Instance MLogic_option : MLogic option.
  Proof.
    constructor.
    { destruct c; simpl; eauto.
      intros. eapply H0; eauto. }
    { simpl; eauto. }
    { destruct x; simpl; auto. }
  Defined.

  Global Instance MLogicZero_option : MLogicZero option.
  Proof.
    constructor.
    { constructor. }
  Defined.

  Global Instance MLogicPlus_option : MLogicPlus option.
  Proof.
    constructor.
    { destruct x; simpl; auto.
      destruct y; simpl; auto. }
  Defined.
End logic_option.
