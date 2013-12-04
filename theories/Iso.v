Require Import ExtLib.Structures.Functor.

Set Implicit Arguments.
Set Strict Implicit.

(** AXIOMS **)
Require Import FunctionalExtensionality.


(** The idea for this file is to describe computational isomorphisms
 ** - A basic isomorphism is just [Iso A B = A <-> B]
 ** - An equivalence is: [Equiv A B = forall F, F A <-> F B]
 **   - This is great but we need to be able to reason about this
 **     when given different [F]s. The key is to require that it
 **     respects all isomorphisms
 **)

Definition compose {T U V : Type} (g : U -> V) (f : T -> U) : T -> V :=
  fun x => g (f x).


Section functorOk.
  Variable F : Type -> Type.

  Class CoFunctor : Type :=
  { cofmap : forall T U, (U -> T) -> F T -> F U }.

  Class FunctorOk (Fun : Functor F) : Type :=
  { fmap_id : forall T,
                fmap (fun x : T => x) = (fun x => x)
  ; fmap_compose : forall T U V (f : T -> U) (g : U -> V),
                     compose (fmap g) (fmap f) = fmap (compose g f)
  }.

  Class CoFunctorOk (CoFun : CoFunctor) : Type :=
  { cofmap_id : forall T,
                cofmap (fun x : T => x) = (fun x => x)
  ; cofmap_compose : forall T U V (f : T -> U) (g : U -> V),
                       compose (cofmap f) (cofmap g) = cofmap (compose g f)
  }.

End functorOk.

Section Iso.
  Variables A B : Type.

  Class Iso : Type := mkIso
  { into : A -> B
  ; outof : B -> A
  }.

  Class IsoOk (iso : Iso) : Type :=
  { into_outof : forall x, into (outof x) = x
  ; outof_into : forall x, outof (into x) = x
  }.
End Iso.

Arguments into {_ _} {iso} _ : rename.
Arguments outof {_ _} {iso} _ : rename.

Definition Iso_ident T : Iso T T :=
{| into := fun x => x
 ; outof := fun x => x
 |}.

Definition IsoOk_ident T : IsoOk (Iso_ident T).
Proof.
  constructor; reflexivity.
Qed.

Definition Iso_flip A B (i : Iso A B) : Iso B A :=
{| into := outof
 ; outof := into
 |}.

Definition IsoOk_flip A B iso (isoOk : @IsoOk A B iso) : IsoOk (Iso_flip iso).
Proof.
  destruct isoOk; constructor; assumption.
Qed.

Section compose.
  Variables A B C : Type.
  Variable iBC : Iso B C.
  Variable iAB : Iso A B.

  Definition Iso_compose : Iso A C :=
  {| into := compose into into
   ; outof := compose outof outof
   |}.

  Variable iokBC : IsoOk iBC.
  Variable iokAB : IsoOk iAB.

  Definition IsoOk_compose : IsoOk Iso_compose.
  Proof.
    constructor; simpl; unfold compose; simpl; intros; repeat (rewrite outof_into || rewrite into_outof); auto.
  Qed.
End compose.

Section IsoFunctor.

  Class IsoFunctor (F : Type -> Type) : Type :=
  { isomap : forall A B, Iso A B -> Iso (F A) (F B) }.

  Class IsoFunctorOk F (iso : IsoFunctor F) : Type :=
  { isomap_id : forall T,
                   isomap {| into := fun x : T => x ; outof := fun x => x |} =
                           {| into := fun x => x ; outof := fun x => x |}
  ; isomap_compose : forall T U V (iTU : Iso T U) (iUV : Iso U V),
                       Iso_compose (isomap iUV) (isomap iTU) = isomap (Iso_compose iUV iTU)
  ; isomap_flip : forall T U (i : Iso T U),
                    Iso_flip (isomap i) = isomap (Iso_flip i)
  }.

  Instance IsoFunctor_Functor (F : Type -> Type) (iso : Functor F) : IsoFunctor F :=
  { isomap := fun _ _ i => {| into :=  fmap (into (iso := i))
                             ; outof := fmap (outof (iso := i)) |} }.

  Instance IsoFunctorOk_Functor f F (Fok : @FunctorOk f F)
  : IsoFunctorOk (IsoFunctor_Functor F).
  Proof.
    constructor.
    { unfold isomap; simpl. intros. rewrite fmap_id; auto. }
    { unfold Iso_compose; simpl; intros. repeat rewrite fmap_compose; eauto. }
    { reflexivity. }
  Qed.

  Instance IsoFunctor_CoFunctor (F : Type -> Type) (iso : CoFunctor F) : IsoFunctor F :=
  { isomap := fun _ _ i => {| into :=  cofmap (outof (iso := i))
                             ; outof := cofmap (into (iso := i)) |} }.

  Instance IsoFunctorOk_CoFunctor f F (Fok : @CoFunctorOk f F)
  : IsoFunctorOk (IsoFunctor_CoFunctor F).
  Proof.
    constructor.
    { unfold isomap; simpl. intros. rewrite cofmap_id; auto. }
    { unfold Iso_compose; simpl; intros. repeat rewrite cofmap_compose; eauto. }
    { reflexivity. }
  Qed.

  Instance IsoFunctor_Fun F G (iF : IsoFunctor F) (iG : IsoFunctor G)
  : IsoFunctor (fun x => F x -> G x) :=
  { isomap := fun _ _ i => {| into := fun i' x =>
                                         let isoF := @isomap _ iF _ _ i in
                                         let isoG := @isomap _ iG _ _ i in
                                         @into _ _  isoG (i' (@outof _ _ isoF x))
                             ; outof := fun i' x =>
                                          let isoF := @isomap _ iF _ _ i in
                                          let isoG := @isomap _ iG _ _ i in
                                          @outof _ _  isoG (i' (@into _ _ isoF x))
                            |} }.
  Instance IsoFunctorOk_Fun F iF (fokF : @IsoFunctorOk F iF)
                            G iG (fokG : @IsoFunctorOk G iG)
  : IsoFunctorOk (IsoFunctor_Fun iF iG).
  Proof.
    constructor; intros. simpl.
    { repeat rewrite isomap_id. simpl. reflexivity. }
    { unfold Iso_compose, compose; simpl.
      f_equal;
      eapply functional_extensionality; intro;
      eapply functional_extensionality; intro;
      repeat match goal with
               | |- appcontext [ @into _ _ ?I (@into _ _ ?J ?X) ] =>
                 change (@into _ _ I (@into _ _ J X)) with (@into _ _ (@Iso_compose _ _ _ I J) X)
               | |- appcontext [ @outof _ _ ?I (@outof _ _ ?J ?X) ] =>
                 change (@outof _ _ I (@outof _ _ J X)) with (@outof _ _ (@Iso_compose _ _ _ J I) X)
             end;
      repeat rewrite isomap_compose; reflexivity. }
    { unfold Iso_flip. simpl.
      f_equal;
      eapply functional_extensionality; intro;
      eapply functional_extensionality; intro;
      repeat match goal with
               | |- _ => progress f_equal
               | |- appcontext [ @outof _ _ ?E ?X ] =>
                 change (@outof _ _ E X) with (@into _ _ (@Iso_flip _ _ E) X) ; rewrite isomap_flip
             end.
      unfold Iso_flip. simpl. destruct i; simpl; reflexivity.
      unfold Iso_flip. simpl. destruct i; simpl; reflexivity. }
  Qed.

  Class DistIsoFunc {A B} (f : forall F, Iso (F A) (F B)) : Prop :=
    dist_over : forall (F : Type -> Type) (func : IsoFunctor F) (fOk : IsoFunctorOk func),
                  isomap (@f (fun x => x)) = f _.

  Instance Functor_eta F (f : Functor F) : Functor (fun x => F x) :=
  { fmap := fun _ _ f => fmap f }.

  Instance FunctorOk_eta F (f : Functor F) (fok : FunctorOk f) : FunctorOk (Functor_eta f).
  Proof.
    constructor. intros. simpl.
    { eapply fmap_id. eauto. }
    { intros; compute.
      eapply fmap_compose. eapply fok. }
  Qed.

  Instance Functor_id : Functor.Functor (fun x => x) :=
  { fmap := fun _ _ f => f }.

  Instance FunctorOk_id : FunctorOk Functor_id.
  Proof.
    constructor; reflexivity.
  Qed.

End IsoFunctor.

Section Equiv.
  Variables A B : Type.

  Class Equiv : Type :=
    siso : forall (F : Type -> Type), Iso (F A) (F B).

  Definition sinto (iso : Equiv) (F : Type -> Type) : F A -> F B :=
    @into (F A) (F B) (siso F).

  Definition soutof (iso : Equiv) (F : Type -> Type) : F B -> F A :=
    @outof (F A) (F B) (siso F).

  Class EquivOk (SI : Equiv) : Type :=
  { siso_dist :> DistIsoFunc (@siso SI)
  ; sinto_soutof_Iso : forall F func, @IsoFunctorOk F func -> IsoOk (@siso SI F)
  }.


(*
  Definition IsIdent {T} (f : T -> T) : Prop :=
    forall x, f x = x.

  Class Respects_IsIdent {T} (F : Type -> Type) (f : (T -> T) -> (F T -> F T)) : Prop :=
  { respects_ident : forall x, IsIdent x -> IsIdent (f x) }.
*)

End Equiv.

Arguments sinto {_ _} {iso} F _ : rename.
Arguments soutof {_ _} {iso} F _ : rename.

Section flip.
  Variables A B : Type.
  Variable E : Equiv A B.

  Definition Equiv_flip : Equiv B A :=
    fun F => Iso_flip (siso F).

  Variable Eok : EquivOk E.

  Definition EquivOk_flip : EquivOk Equiv_flip.
  Proof.
    destruct Eok.
    constructor.
    { red; intros.
      specialize (siso_dist0 F _ _).
      unfold siso, Equiv_flip.
      rewrite <- isomap_flip.
      f_equal.
      rewrite <- siso_dist0. reflexivity. }
    { unfold Equiv_flip; simpl. intros.
      eapply IsoOk_flip. eauto. }
  Qed.
End flip.

Section ident.
  Variable A : Type.

  Definition Equiv_ident : Equiv A A :=
    fun F => {| into := fun x : F A => x ; outof := fun x : F A => x |}.

  Global Instance EquivOk_ident : EquivOk Equiv_ident.
  Proof.
    constructor.
    { red. simpl. destruct 1. eauto. }
    { constructor; reflexivity. }
  Qed.
End ident.

Section Equiv_compose.
  Variables A B C : Type.
  Variable Equiv_AB : Equiv A B.
  Variable Equiv_BC : Equiv B C.

  Definition Equiv_compose : Equiv A C :=
    fun F => Iso_compose (siso F) (siso F).

  Hypothesis EquivOk_AB : EquivOk Equiv_AB.
  Hypothesis EquivOk_BC : EquivOk Equiv_BC.

  Global Instance EquivOk_compose : EquivOk Equiv_compose.
  Proof.
    constructor.
    { red. intros.
      unfold siso, Equiv_compose.
      rewrite <- (@siso_dist _ _ _ EquivOk_AB _ _ fOk).
      rewrite <- (@siso_dist _ _ _ EquivOk_BC _ _ fOk).
      generalize (@isomap_compose _ _ fOk _ _ _ (@siso A B Equiv_AB (fun x : Type => x)) (@siso _ _ Equiv_BC (fun x : Type => x))).
      eauto. }
    { simpl; intros. eapply IsoOk_compose; simpl;
      eapply sinto_soutof_Iso; eauto. }
  Qed.
End Equiv_compose.
