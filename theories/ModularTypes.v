Require Import ExtLib.Data.Vector.
Require Import ExtLib.Data.SigT.
Require Import ExtLib.Tactics.
Require Import MirrorCore.TypesI.

Universes Usmall Ularge.

Section parametric.
  Fixpoint type_for_arity (n : nat) : Type@{Ularge} :=
    match n with
    | 0 => Type@{Usmall}
    | S n => Type@{Usmall} -> type_for_arity n
    end.

  Fixpoint applyn' {n} (vs : vector Type@{Usmall} n)
  : type_for_arity n -> Type@{Usmall} :=
    match vs in vector _ n return type_for_arity n -> Type@{Usmall} with
    | Vnil _ => fun T => T
    | Vcons v vs => fun F => applyn' vs (F v)
    end.
  Definition applyn {n} (f : type_for_arity n) (vs : vector Type@{Usmall} n)
  : Type@{Usmall} :=
    applyn' vs f.

  Variable symbol : nat -> Type.

  Variable symbolD : forall {n}, symbol n -> type_for_arity n.

  Variable symbol_eq : forall {n} (a b : symbol n), option (a = b).
  Variable symbol_dec : forall {n} (a b : symbol n), {a = b} + {a <> b}.
  Variable symbol_eq_total : forall n a b,
      @symbol_eq n a b = match @symbol_dec n a b with
                         | left x => Some x
                         | right _ => None
                         end.

  Arguments symbolD {_} _.
  Arguments symbol_dec {_} _ _.
  Arguments symbol_eq {_} _ _.

  Unset Elimination Schemes.

  Inductive mtyp : Type :=
  | tyArr : mtyp -> mtyp -> mtyp
  | tyBase0 : symbol 0 -> mtyp
  | tyBase1 : symbol 1 -> mtyp -> mtyp
  | tyBase2 : symbol 2 -> mtyp -> mtyp -> mtyp
  | tyApp : forall {n}, symbol (3 + n) -> vector mtyp (3 + n) -> mtyp.

  Section mtyp_ind.
    Variable P : mtyp -> Prop.
    Hypotheses  (Harr : forall {a b}, P a -> P b -> P (tyArr a b))
                (Hbase0 : forall s, P (tyBase0 s))
                (Hbase1 : forall s {a}, P a -> P (tyBase1 s a))
                (Hbase2 : forall s {a b}, P a -> P b -> P (tyBase2 s a b))
                (Happ : forall {n} s ms, ForallV P ms -> P (@tyApp n s ms)).
    Fixpoint mtyp_ind (x : mtyp) : P x :=
      match x as x return P x with
      | tyArr a b => Harr _ _ (mtyp_ind a) (mtyp_ind b)
      | tyBase0 s => Hbase0 s
      | tyBase1 s a => Hbase1 s _ (mtyp_ind a)
      | tyBase2 s a b => Hbase2 s _ _ (mtyp_ind a) (mtyp_ind b)
      | tyApp s ms =>
        Happ _ s ms ((fix all {n} (ms : vector mtyp n) : ForallV P ms :=
                        match ms with
                        | Vnil _ => ForallV_nil _
                        | Vcons m ms => ForallV_cons _(mtyp_ind m) (all ms)
                        end) _ ms)
      end.
  End mtyp_ind.

  Set Elimination Schemes.

  (** Better to match on vector? *)

  Fixpoint mtypD (t : mtyp) : Type@{Usmall} :=
    match t return Type@{Usmall} with
    | tyArr a b => mtypD a -> mtypD b
    | tyBase0 s => symbolD s
    | tyBase1 s m => symbolD s (mtypD m)
    | tyBase2 s m1 m2 => symbolD s (mtypD m1) (mtypD m2)
    | tyApp s ms => applyn (symbolD s) (vector_map mtypD ms)
    end.

  Instance Injective_tyApp {n n'} {s : symbol (3+n)} {s' : symbol (3+n')}
           ms ms' : Injective (tyApp s ms = tyApp s' ms') :=
  { result := forall pf : n' = n,
      s = match pf with eq_refl => s' end /\
      ms = match pf with eq_refl => ms' end }.
  Proof.
    intros. subst.
    inversion H.
    inv_all. tauto.
  Defined.

  Fixpoint mtyp_dec (a b : mtyp) : {a = b} + {a <> b}.
  refine
    match a as a , b as b return {a = b} + {a <> b} with
    | tyArr l r , tyArr l' r' =>
      match mtyp_dec l l'
          , mtyp_dec r r'
      with
      | left pf , left pf' => left match pf , pf' with
                                   | eq_refl , eq_refl => eq_refl
                                   end
      | _ , _ => right _
      end
    | tyBase0 s , tyBase0 s' =>
      match symbol_dec s s' with
      | left pf => left match pf with eq_refl => eq_refl end
      | _ => right _
      end
    | tyBase1 s m , tyBase1 s' m' =>
      match symbol_dec s s'
          , mtyp_dec m m'
      with
      | left pf , left pf' => left match pf , pf' with
                                   | eq_refl , eq_refl => eq_refl
                                   end
      | _ , _ => right _
      end
    | tyBase2 s m m2 , tyBase2 s' m' m2' =>
      match symbol_dec s s'
          , mtyp_dec m m'
          , mtyp_dec m2 m2'
      with
      | left pf , left pf' , left pf'' =>
        left match pf , pf' , pf'' with
             | eq_refl , eq_refl , eq_refl => eq_refl
             end
      | _ , _ , _ => right _
      end
    | @tyApp n s ms , @tyApp n' s' ms' =>
      match PeanoNat.Nat.eq_dec n' n with
      | left pf =>
        match symbol_dec s match pf with eq_refl => s' end
            , vector_dec mtyp_dec ms match pf with eq_refl => ms' end
        with
        | left pf , left pf' => left _
        | _ , _ => right _
        end
      | right _ => right _
      end
    | _ , _ => right _
    end; try solve [ subst; reflexivity
                   | intro; congruence
                   | intro H; inversion H; congruence ].
  intro. subst. apply n0.
  inv_all. specialize (H eq_refl). simpl in H.
  tauto.
  subst. intro. apply n0.
  clear - H. inv_all. specialize (H eq_refl). tauto.
  Defined.

  Fixpoint mtyp_cast (a b : mtyp) : option (a = b).
  refine
    match a as a , b as b return option (a = b) with
    | tyArr l r , tyArr l' r' =>
      match mtyp_cast l l'
          , mtyp_cast r r'
      with
      | Some pf , Some pf' => Some match pf , pf' with
                                   | eq_refl , eq_refl => eq_refl
                                   end
      | _ , _ => None
      end
    | tyBase0 s , tyBase0 s' =>
      match symbol_dec s s' with
      | left pf => Some match pf with eq_refl => eq_refl end
      | _ => None
      end
    | tyBase1 s m , tyBase1 s' m' =>
      match symbol_dec s s'
          , mtyp_cast m m'
      with
      | left pf , Some pf' => Some match pf , pf' with
                                   | eq_refl , eq_refl => eq_refl
                                   end
      | _ , _ => None
      end
    | tyBase2 s m m2 , tyBase2 s' m' m2' =>
      match symbol_dec s s'
          , mtyp_cast m m'
          , mtyp_cast m2 m2'
      with
      | left pf , Some pf' , Some pf'' =>
        Some match pf , pf' , pf'' with
             | eq_refl , eq_refl , eq_refl => eq_refl
             end
      | _ , _ , _ => None
      end
    | @tyApp n s ms , @tyApp n' s' ms' =>
      match PeanoNat.Nat.eq_dec n' n with
      | left pf =>
        match symbol_dec s match pf with eq_refl => s' end
            , vector_dec mtyp_dec ms match pf with eq_refl => ms' end
        with
        | left pf , left pf' => Some _
        | _ , _ => None
        end
      | right _ => None
      end
    | _ , _ => None
    end.
  subst. reflexivity.
  Defined.

  Inductive mtyp_acc (a : mtyp) : mtyp -> Prop :=
  | tyAcc_tyArrL   : forall b, mtyp_acc a (tyArr a b)
  | tyAcc_tyArrR   : forall b, mtyp_acc a (tyArr b a)
  | tyAcc_tyBase1  : forall s, mtyp_acc a (tyBase1 s a)
  | tyAcc_tyBase2L : forall s b, mtyp_acc a (tyBase2 s a b)
  | tyAcc_tyBase2R : forall s b, mtyp_acc a (tyBase2 s b a)
  | tyAcc_tyApp    : forall n s ms, vector_In a ms -> mtyp_acc a (@tyApp n s ms).



  Theorem wf_mtyp_acc : well_founded mtyp_acc.
  Proof using.
    red.
    induction a; constructor; inversion 1; subst; auto.
    - inv_all. subst. eapply ForallV_vector_In; eauto.
  Defined.
      

  Instance RType_typ0 : RType mtyp :=
  { typD := mtypD
  ; type_cast := mtyp_cast
  ; tyAcc := mtyp_acc }.

  Local Instance EqDec_symbol : forall n, EqDec (symbol n) (@eq (symbol n)).
  Proof.
    red. intros.
    destruct (symbol_dec x y); (left + right); assumption.
  Defined.

  Local Instance EqDec_mtyp : EqDec mtyp (@eq mtyp).
  Proof.
    red. intros.
    eapply mtyp_dec.
  Defined.

  Lemma dec_refl
  : forall T (dec : forall a b : T, {a = b} + {a <> b}) (a : T),
      dec a a = left eq_refl.
  Proof using.
    intros. destruct (dec a a).
    - uip_all. reflexivity.
    - exfalso; tauto.
      Unshelve. assumption.
  Qed.

  Lemma symbol_dec_refl : forall n (a : symbol n), symbol_dec a a = left eq_refl.
  Proof using.
    intro. apply dec_refl.
  Qed.

  Theorem mtyp_cast_refl : forall a,
      mtyp_cast a a = Some eq_refl.
  Proof.
    induction a; simpl.
    - rewrite IHa1. rewrite IHa2. reflexivity.
    - rewrite symbol_dec_refl. reflexivity.
    - rewrite symbol_dec_refl. rewrite IHa. reflexivity.
    - rewrite symbol_dec_refl. rewrite IHa1; rewrite IHa2; reflexivity.
    - repeat rewrite dec_refl. reflexivity.
  Qed.

  Instance RTypeOk_typ0 : RTypeOk.
  Proof.
    constructor.
    - reflexivity.
    - eapply wf_mtyp_acc.
    - destruct pf; reflexivity.
    - destruct pf1; destruct pf2; reflexivity.
    - apply mtyp_cast_refl.
    - eauto with typeclass_instances.
  Qed.

  Instance Typ0_sym (s : symbol 0) : Typ0 _ (symbolD s) :=
  { typ0 := tyBase0 s
  ; typ0_cast := eq_refl
  ; typ0_match := fun T (t : mtyp) tr =>
    match t as t'
          return T (mtypD t') -> T (mtypD t')
    with
    | tyBase0 s' =>
      match symbol_dec s s' with
      | left pf => fun _ => match pf with
                            | eq_refl => tr
                            end
      | right _ => fun fa => fa
      end
    | _ => fun fa => fa
    end }.
  Instance Typ0Ok_sym (s : symbol 0) : Typ0Ok (Typ0_sym s).
  Proof using.
    constructor.
    { simpl. intros.
      destruct (symbol_dec s s) eqn:?; try reflexivity.
      - uip_all. reflexivity.
      - exfalso; clear - n. congruence. }
    { intro.
      destruct x; try solve [ right ; eauto ].
      simpl. destruct (symbol_dec s s0); try solve [ right ; eauto ].
      left. subst. exists eq_refl. reflexivity. }
    { destruct pf. reflexivity. }
  Qed.

  Instance Typ1_sym (s : symbol 1) : Typ1 _ (symbolD s) :=
  { typ1 := tyBase1 s
  ; typ1_cast := fun _ => eq_refl
  ; typ1_match := fun T (t : mtyp) tr =>
      match t as t return T (mtypD t) -> T (mtypD t) with
      | tyBase1 s' m =>
        match symbol_dec s s' with
        | left pf => fun _ => match pf with
                              | eq_refl => tr m
                              end
        | _ => fun fa => fa
        end
      | _ => fun fa => fa
      end }.

  Instance Typ1Ok_sym (s : symbol 1) : Typ1Ok (Typ1_sym s).
  Proof using.
    constructor.
    { simpl. intros.
      rewrite dec_refl. reflexivity. }
    { intros. constructor. }
    { compute. inversion 1. reflexivity. }
    { destruct x; try solve [ right ; eauto ].
      simpl. destruct (symbol_dec s s0); try solve [ right ; eauto ].
      subst. left. eexists. exists eq_refl. reflexivity. }
    { destruct pf. reflexivity. }
  Qed.

  Instance Typ2_sym (s : symbol 2) : Typ2 _ (symbolD s) :=
  { typ2 := tyBase2 s
  ; typ2_cast := fun _ _ => eq_refl
  ; typ2_match := fun T (t : mtyp) tr =>
      match t as t return T (mtypD t) -> T (mtypD t) with
      | tyBase2 s' m m' =>
        match symbol_dec s s' with
        | left pf => fun _ => match pf with
                              | eq_refl => tr m m'
                              end
        | _ => fun fa => fa
        end
      | _ => fun fa => fa
      end }.

  Instance Typ2Ok_sym (s : symbol 2) : Typ2Ok (Typ2_sym s).
  Proof using.
    constructor.
    { simpl. intros.
      rewrite dec_refl. reflexivity. }
    { constructor. }
    { constructor. }
    { compute. inversion 1. tauto. }
    { destruct x; try solve [ right ; eauto ].
      simpl. destruct (symbol_dec s s0); try solve [ right ; eauto ].
      subst. left. do 2 eexists. exists eq_refl. reflexivity. }
    { destruct pf. reflexivity. }
  Qed.

  Instance Typ2_Fun : Typ2 _ RFun :=
  { typ2 := tyArr
  ; typ2_cast := fun _ _ => eq_refl
  ; typ2_match := fun T (x : mtyp) tr =>
    match x as x return T (mtypD x) -> T (mtypD x) with
    | tyArr l r => fun _ => tr l r
    | _ => fun fa => fa
    end }.

  Instance Typ2Ok_Fun : Typ2Ok Typ2_Fun.
  Proof using.
    constructor.
    { reflexivity. }
    { constructor. }
    { constructor. }
    { inversion 1. split; reflexivity. }
    { destruct x; try solve [ right ; eauto ].
      simpl. left; do 2 eexists; exists eq_refl; reflexivity. }
    { destruct pf. reflexivity. }
  Qed.

End parametric.