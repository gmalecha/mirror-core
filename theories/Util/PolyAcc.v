(** Polymorphic accesibility relation *)
Section Pwf.
  Variable T : Type.
  Variable F : T -> Type.
  Variable R : forall a b, F a -> F b -> Prop.

  Inductive PAcc a (x : F a) : Prop :=
  | PAcc_intro : (forall b (y : F b), R _ _ y x -> PAcc _ y) -> PAcc _ x.

  Definition Pwell_founded : Prop :=
    forall a x, PAcc a x.

  Section PFix.
    Variable P : forall t, F t -> Type.
    Variable Pwf_R : Pwell_founded.
    Variable (rec : forall a (x : F a), (forall b (y : F b), R _ _ y x -> P _ y) -> P _ x).
    Definition PFix (a : T) (x : F a) : P a x.
      refine
        ((fix recurse (a : T) (x : F a) (acc : PAcc _ x) {struct acc} : P a x :=
            match acc with
            | @PAcc_intro _ _ rec' => rec _ _ (fun b y pf => recurse b y (rec' _ _ pf))
            end) a x (Pwf_R _ _)).
    Defined.

  End PFix.

  Theorem Pwell_founded_well_founded
    : Pwell_founded -> forall t, well_founded (R t t).
  Proof.
    unfold Pwell_founded, well_founded.
    intros.
    specialize (H _ a).
    induction H.
    constructor.
    eauto.
  Defined.

  Inductive PleftTrans : forall a b, F a -> F b -> Prop :=
  | Pstep : forall a b (x : F a) (y : F b), R _ _ x y -> PleftTrans _ _ x y
  | Ptrans : forall a b c (x : F a) (y : F b) (z : F c),
      R _ _ x y -> PleftTrans _ _ y z -> PleftTrans _ _ x z.

End Pwf.

Theorem Pwell_founded_PleftTrans : forall {T} {F : T -> Type} (R : forall a b : T, F a -> F b -> Prop),
    Pwell_founded _ _ R -> Pwell_founded _ _ (PleftTrans _ _ R).
Proof.
  clear.
  do 3 intro.
  refine (fun f => @PFix _ _ _ _ f _).
  clear.
  intros; constructor; intros.
  revert H.
  induction H0.
  { eauto. }
  { intros. eapply IHPleftTrans; [ eapply H1 | eapply Pstep; auto ]. }
Qed.
