Require Import ExtLib.Structures.Functor.

(** AXIOMS **)
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Set Strict Implicit.

(** The idea for this file is to describe computational isomorphisms
 ** - A basic isomorphism is just [Iso A B = A <-> B]
 ** - An equivalence is: [Equiv A B = forall F, F A <-> F B]
 **   - This is great but we need to be able to reason about this
 **     when given different [F]s. The key is to require that it
 **     respects all isomorphisms
 **)

Section functorOk.
  Variable F : Type -> Type.

  Class CoFunctor : Type :=
  { cofmap : forall T U, (U -> T) -> F T -> F U }.

  Class DualFunctor : Type :=
  { dualfmap : forall T U, (T -> U) -> (U -> T) -> F T -> F U }.


  Class FunctorOk (Fun : Functor F) : Type :=
  { fmap_id : forall T,
                fmap (fun x : T=> x) = (fun x => x)
  }.

  Class CoFunctorOk (CoFun : CoFunctor) : Type :=
  { cofmap_id : forall T,
                cofmap (fun x : T => x) = (fun x => x)
  }.

  Class DualFunctorOk (DualFun : DualFunctor) : Type :=
  { dualfmap_id : forall T,
                dualfmap (fun x : T => x) (fun x => x) = (fun x => x)
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

  Class Equiv : Type :=
  { siso : forall (F : Type -> Type), F A -> F B }.

  Definition sinto (iso : Equiv) (F : Type -> Type) : F A -> F B :=
    siso F.

  Definition soutof (iso : Equiv) (F : Type -> Type) : F B -> F A :=
    siso (fun x => F x -> F A) (fun x => x).

(*
  Definition IsIdent {T} (f : T -> T) : Prop := 
    forall x, f x = x.

  Class Respects_IsIdent {T} (F : Type -> Type) (f : (T -> T) -> (F T -> F T)) : Prop :=
  { respects_ident : forall x, IsIdent x -> IsIdent (f x) }.
*)

End Iso.

Arguments into {_ _} {iso} _ : rename.
Arguments outof {_ _} {iso} _ : rename.

Section Equiv.

  Class IsoFunctor (F : Type -> Type) : Type :=
  { isofmap : forall A B, Iso A B -> Iso (F A) (F B) }.

  Class IsoFunctorOk F (iso : IsoFunctor F) : Type :=
  { isofmap_id : forall T,
                   isofmap {| into := fun x : T => x ; outof := fun x => x |} = 
                           {| into := fun x => x ; outof := fun x => x |} }.

  Instance IsoFunctor_Functor (F : Type -> Type) (iso : Functor F) : IsoFunctor F :=
  { isofmap := fun _ _ i => {| into :=  fmap (into (iso := i)) 
                             ; outof := fmap (outof (iso := i)) |} }.

  Instance IsoFunctorOk_IsoFunctor_Functor f F (Fok : @FunctorOk f F) 
  : IsoFunctorOk (IsoFunctor_Functor F).
  Proof.
    constructor.
    unfold isofmap; simpl. intros. rewrite fmap_id; auto.
  Qed.
    

  Instance IsoFunctor_CoFunctor (F : Type -> Type) (iso : CoFunctor F) : IsoFunctor F :=
  { isofmap := fun _ _ i => {| into :=  cofmap (outof (iso := i)) 
                             ; outof := cofmap (into (iso := i)) |} }.

  Instance IsoFunctorOk_IsoFunctor_CoFunctor f F (Fok : @CoFunctorOk f F) 
  : IsoFunctorOk (IsoFunctor_CoFunctor F).
  Proof.
    constructor.
    unfold isofmap; simpl. intros. rewrite cofmap_id; auto.
  Qed.

  Definition flipIso {A B} (iso : Iso A B) : Iso B A :=
  {| into := outof ; outof := into |}.

  Definition IsoOk_flipIso A B iso (isoOk : @IsoOk A B iso) : IsoOk (flipIso iso).
  Proof.
    destruct isoOk; constructor; assumption.
  Qed.

  Instance IsoFunctor_Fun F G (iF : IsoFunctor F) (iG : IsoFunctor G)
  : IsoFunctor (fun x => F x -> G x) :=
  { isofmap := fun _ _ i => {| into := fun i' x => 
                                         let isoF := @isofmap _ iF _ _ i in
                                         let isoG := @isofmap _ iG _ _ i in
                                         @into _ _  isoG (i' (@outof _ _ isoF x))
                             ; outof := fun i' x => 
                                          let isoF := @isofmap _ iF _ _ i in
                                          let isoG := @isofmap _ iG _ _ i in
                                          @outof _ _  isoG (i' (@into _ _ isoF x))
                            |} }.
  Instance IsoFunctorOk_Fun F iF (fokF : @IsoFunctorOk F iF) 
                            G iG (fokG : @IsoFunctorOk G iG) 
  : IsoFunctorOk (IsoFunctor_Fun iF iG).
  Proof.
    constructor; intros. simpl.
    repeat rewrite isofmap_id. simpl.
    reflexivity.
  Qed.   

  Class DistIsoFunc {A B} (f : forall F, Iso (F A) (F B)) : Prop :=
    dist_over : forall (F : Type -> Type) (func : IsoFunctor F) (fOk : IsoFunctorOk func),
      isofmap (@f (fun x => x)) = f _.

  Class EquivOk A B (SI : Equiv A B) : Type :=
  { siso_dist :> DistIsoFunc (fun F => {| into := sinto SI F ; outof := soutof SI F |})
  ; sinto_soutof_Iso : forall F, IsoOk {| into := sinto SI F ; outof := soutof SI F |}
  }.

(*
  Definition flipEquiv A B (e : Equiv A B) : Equiv B A :=
  {| siso := fun F => siso (fun x => F x -> F A) (fun x => x) |}.

  Instance EquivOk_flipEquiv A B e (eok : @EquivOk A B e) : EquivOk (flipEquiv e).
  Proof.
    destruct eok; constructor.
    { simpl. red; intros.
      specialize (siso_dist0 _ _ fOk); simpl in *.
      unfold sinto, soutof in *.
*)

End Equiv.

Arguments into {_ _} {iso} _ : rename.
Arguments outof {_ _} {iso} _ : rename.
Arguments sinto {_ _} {iso} F _ : rename.
Arguments soutof {_ _} {iso} F _ : rename.

Section iso_tac.
  Variable A B : Type.
  
  Definition Functor_const T : Functor (fun x => T) :=
  {| fmap := fun T' U' (f : T' -> U') (x : T) => x |}.

  Instance FunctorOk_const T : FunctorOk (Functor_const T).
  Proof.
    constructor; compute. reflexivity.
  Qed.

  Definition Functor_option : Functor option :=
  {| fmap := fun _ _ f x => match x with
                              | None => None
                              | Some x => Some (f x)
                            end |}.

  Instance FunctorOk_option : FunctorOk Functor_option.
  Proof.
    constructor; compute.
    intros. apply functional_extensionality. destruct x; reflexivity.
  Qed.

  Variable iso : forall F, Iso (F A) (F B).
  Context {isoOk : forall F, IsoOk (iso F)}.
  Context {DistFunc_f : DistIsoFunc iso}.

  Local Instance Functor_Fun T : Functor (fun x => T -> x) :=
  {| fmap := fun _ _ g f => fun x => g (f x) |}.

  Local Instance CoFunctor_Fun T : CoFunctor (fun x => x -> T) :=
  {| cofmap := fun _ _ g f => fun x => f (g x) |}.

  Local Instance Functor_functor F G (fF : Functor F) (fG : Functor G) : Functor (fun x => F (G x)) :=
  {| fmap := fun _ _ g => @fmap F _ _ _ (@fmap G _ _ _ g) |}.

  Local Instance CoFunctor_functor F G (fF : Functor F) (fG : CoFunctor G) : CoFunctor (fun x => F (G x)) :=
  {| cofmap := fun _ _ g => @fmap F _ _ _ (@cofmap G _ _ _ g) |}.

  Local Instance Functor_cofunctor F G (fF : CoFunctor F) (fG : Functor G) : CoFunctor (fun x => F (G x)) :=
  {| cofmap := fun _ _ g => @cofmap F _ _ _ (@fmap G _ _ _ g) |}.

  Local Instance CoFunctor_cofunctor F G (fF : CoFunctor F) (fG : CoFunctor G) : Functor (fun x => F (G x)) :=
  {| fmap := fun _ _ g => @cofmap F _ _ _ (@cofmap G _ _ _ g) |}.

  Lemma f_const : forall T x, into (iso := iso (fun _ => T)) x = x.
  Proof.
    intro. 
    specialize (@dist_over _ _ _ DistFunc_f _ (IsoFunctor_Functor (Functor_const T))); simpl; intros.
    match goal with
      | [ H : _ -> _ = ?X |- context [ ?Y ] ] =>
        replace Y with X; [ rewrite <- H | ]; try reflexivity
    end.
    eapply IsoFunctorOk_IsoFunctor_Functor; eauto with typeclass_instances.
  Qed.

  Instance IsoFunctor_compose F (fF : IsoFunctor F) G (fG : IsoFunctor G) 
  : IsoFunctor (fun x => F (G x)) :=
  {| isofmap := fun A B (i : Iso A B) => @isofmap _ fF _ _ (@isofmap _ fG _ _ i) |}.

  Global Instance IsoFunctorOk_compose 
         F fF (fokF : @IsoFunctorOk F fF) 
         G fG (fokG : @IsoFunctorOk G fG) 
  : IsoFunctorOk (IsoFunctor_compose fF fG).
  Proof.
    constructor.
    intros. simpl. repeat rewrite isofmap_id. reflexivity.
  Qed.

  Lemma f_option : forall F (fF : IsoFunctor F) (fFok : IsoFunctorOk fF) x, 
                     into (iso := iso (fun T => option (F T))) x = 
                     match x with
                       | None => None
                       | Some x => Some (into (iso := iso (fun T => (F T))) x)
                     end.
  Proof.
    intros.
    assert (IsoFunctorOk (IsoFunctor_compose (IsoFunctor_Functor Functor_option) fF)).
    { eapply IsoFunctorOk_compose; eauto.
      eapply IsoFunctorOk_IsoFunctor_Functor. eauto with typeclass_instances. }
    specialize (@dist_over _ _ _ DistFunc_f _ _ H); simpl; intros.
    match goal with
      | [ H : _ = ?X |- context [ ?Y ] ] =>
        replace Y with X; [ rewrite <- H | ]; try reflexivity
    end.
    simpl. destruct x; auto.
    f_equal. rewrite dist_over; auto.
  Qed.

  Definition compose {T U V : Type} (g : U -> V) (f : T -> U) : T -> V :=
    fun x => g (f x).

  Lemma f_Fun : forall F G (fF : IsoFunctor F) (fG : IsoFunctor G),
                  IsoFunctorOk fG -> IsoFunctorOk fF ->
                  forall (x : F A -> G A),
                  into (iso := iso (fun T => F T -> G T)) x = 
                  compose (into (iso := iso G)) (compose x (outof (iso := iso F))).
  Proof.
    intros.
    unfold compose.
    assert (IsoFunctorOk (IsoFunctor_Fun fF fG)).
    { apply IsoFunctorOk_Fun; auto. }
    specialize (@dist_over _ _ _ _ _ _ H1); simpl; intros.
    match goal with
      | [ H : _ = ?X |- context [ ?Y ] ] =>
        replace Y with X; [ rewrite <- H | ]; try reflexivity
    end.
    simpl. 
    repeat rewrite dist_over by assumption. reflexivity.
  Qed.

End iso_tac.

Create HintDb iso discriminated.

Section with_iso.
  Variable A B : Type.
  Variable SI : Equiv A B.
  Variable SIOk : EquivOk SI.

(*
  Theorem sinto_soutof : forall R x, sinto R (soutof R x) = x.
  Proof.
    intros. unfold sinto, soutof. 
    destruct (sinto_soutof_Iso R); auto.    

  Hint Rewrite sinto_soutof soutof_sinto : iso.
*)

  Let iso : forall F, Iso (F A) (F B) :=
    fun F => {| into := sinto F ; outof := soutof F |}.
  Lemma isoOk : forall F, IsoOk (iso F).
  Proof.
    intros. apply sinto_soutof_Iso.
  Qed.
  Lemma DistFunc_f : DistIsoFunc iso.
  Proof.
    intros. apply siso_dist.
  Qed.

  Let fiso : forall F, Iso (F B) (F A) :=
    fun F => flipIso (iso F).
  Lemma fisoOk : forall F, IsoOk (fiso F).
  Proof.
    intros. eapply IsoOk_flipIso. apply isoOk.
  Qed.
  Lemma fDistFunc_f : DistIsoFunc fiso.
  Proof.
    intros. unfold fiso. unfold flipIso. simpl. 
  Admitted.

  Lemma sinto_option : forall (T : Type -> Type) fT x, @IsoFunctorOk T fT ->
                         sinto (iso := SI) (fun Ty => option (T Ty)) x =
                         match x with
                           | None => None
                           | Some x => Some (sinto (iso := SI) (fun Ty => T Ty) x)
                         end.
  Proof.
    intros. 
    generalize (@f_option A B iso DistFunc_f _ _ H x).
    simpl. auto.
  Qed.

  Lemma soutof_option : forall (T : Type -> Type) fT x, @IsoFunctorOk T fT ->
                         soutof (iso := SI) (fun Ty => option (T Ty)) x =
                         match x with
                           | None => None
                           | Some x => Some (soutof (iso := SI) (fun Ty => T Ty) x)
                         end.
  Proof.
    intros. 
    generalize (@f_option _ _ fiso fDistFunc_f _ _ H x).
    simpl. auto.
  Qed.
  Hint Rewrite sinto_option soutof_option : iso.
  Lemma sinto_const : forall (T : Type) x,
                        sinto (iso := SI) (fun _ => T) x = x.
  Proof.
    intros. 
    generalize (@f_const _ _ iso DistFunc_f _ x).
    simpl. auto.
  Qed.
  Lemma soutof_const : forall (T : Type) x,
                        soutof (iso := SI) (fun _ => T) x = x.
  Proof.
    intros. 
    generalize (@f_const _ _ fiso fDistFunc_f _ x).
    simpl. auto.
  Qed.
  Hint Rewrite sinto_const soutof_const : iso.

  Lemma sinto_app : forall T U fT fU,
                      @IsoFunctorOk T fT ->
                      @IsoFunctorOk U fU ->
                      forall (f : T A -> U A),
                      sinto (iso := SI) (fun Ty => T Ty -> U Ty) f = 
                      (fun x => (sinto (iso := SI) (fun Ty => U Ty) (f (soutof _ x)))). 
  Proof.
    intros.
    generalize (@f_Fun _ _ iso DistFunc_f _ _ _ _ H0 H f).
    simpl. auto.
  Qed.
  Lemma soutof_app : forall T U fT fU,
                      @IsoFunctorOk T fT ->
                      @IsoFunctorOk U fU ->
                      forall (f : T B -> U B),
                      soutof (iso := SI) (fun Ty => T Ty -> U Ty) f = 
                      (fun x => (soutof (iso := SI) (fun Ty => U Ty) (f (sinto _ x)))). 
  Proof.
    intros.
    generalize (@f_Fun _ _ fiso fDistFunc_f _ _ _ _ H0 H f).
    simpl. auto.
  Qed.
  Hint Rewrite sinto_app soutof_app : iso.

  Theorem soutof_app' : forall T U fU,
                          @IsoFunctorOk U fU ->
                          forall f,
                         soutof (fun Ty => T -> U Ty) f =
                         (fun x => (soutof U (f x))).
  Proof.
    intros.
    rewrite (@soutof_app _ _ _ _ (IsoFunctorOk_IsoFunctor_Functor (FunctorOk_const T)) H f).
    apply functional_extensionality; intros. rewrite sinto_const. reflexivity.
  Qed.
  Theorem sinto_app' : forall T U fU,
                          @IsoFunctorOk U fU ->
                          forall f,
                         sinto (fun Ty => T -> U Ty) f =
                         (fun x => (sinto U (f x))).
  Proof.
    intros.
    rewrite (@sinto_app _ _ _ _ (IsoFunctorOk_IsoFunctor_Functor (FunctorOk_const T)) H f).
    apply functional_extensionality; intros. rewrite soutof_const. reflexivity.
  Qed.
    
  Theorem soutof_app'' : forall T U fU,
                          @IsoFunctorOk U fU ->
                           forall f,
                         soutof (fun Ty => U Ty -> T) f =
                         (fun x => f (sinto U x)).
  Proof.
    intros.
    rewrite (@soutof_app _ _ _ _ H (IsoFunctorOk_IsoFunctor_Functor (FunctorOk_const T)) f).
    apply functional_extensionality; intros. rewrite soutof_const. reflexivity.
  Qed.

  Theorem sinto_app'' : forall T U fU,
                          @IsoFunctorOk U fU ->
                           forall f,
                         sinto (fun Ty => U Ty -> T) f =
                         (fun x => f (soutof U x)).
  Proof.
    intros.
    rewrite (@sinto_app _ _ _ _ H (IsoFunctorOk_IsoFunctor_Functor (FunctorOk_const T)) f).
    apply functional_extensionality; intros. rewrite sinto_const. reflexivity.
  Qed.

  Hint Rewrite sinto_app sinto_app' sinto_app'' using eauto with typeclass_instances : iso.
  Hint Rewrite soutof_app soutof_app' soutof_app'' using eauto with typeclass_instances : iso.
End with_iso.

Ltac rewrite_iso :=
  autorewrite with iso in *.
