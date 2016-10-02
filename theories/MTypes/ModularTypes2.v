Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Vector.
Require Import ExtLib.Data.SigT.
Require Import ExtLib.Data.POption.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.
Require Import ExtLib.Data.Eq.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.Views.TypeView.

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

  Class TSym : Type :=
  { symbolD : forall {n}, symbol n -> type_for_arity n
(*  ; symbol_eq : forall {n} (a b : symbol n), option (a = b) *)
  ; symbol_dec : forall {n} (a b : symbol n), {a = b} + {a <> b}
(*
  ; symbol_eq_total : forall n a b,
      @symbol_eq n a b = match @symbol_dec n a b with
                         | left x => Some x
                         | right _ => None
                         end
*)
  }.

  Variable ts : TSym.

  Unset Elimination Schemes.

  Inductive mtyp : nat -> Type :=
  | tyArr : mtyp 0 -> mtyp 0 -> mtyp 0
  | tyApp : forall {n}, mtyp (S n) -> mtyp 0 -> mtyp n
(*
  | tyInj0 : symbol 0 -> mtyp 0
  | tyInj1 : symbol 1 -> mtyp 1
  | tyInj2 : symbol 2 -> mtyp 2
  | tyInjN : forall {n}, symbol (3 + n) -> mtyp (3 + n)
*)
  | tyInj : forall n, symbol n -> mtyp n
  | tyProp : mtyp 0
  | tyVar : forall n, positive -> mtyp n. (** Reserved for unification, do not use **)

  Section mtyp_ind.
    Variable P : forall {n}, mtyp n -> Prop.
    Hypotheses  (Harr : forall {a b : mtyp 0}, P _ a -> P _ b -> P _ (tyArr a b))
                (Happ : forall n {a : mtyp (S n)} {b : mtyp 0}, P _ a -> P _ b -> P _ (tyApp a b))
                (*(Hinj0 : forall s, P _ (tyInj0 s))
                (Hinj1 : forall s, P _ (tyInj1 s))
                (Hinj2 : forall s, P _ (tyInj2 s))
                (Hinj : forall {n} s, P (3+n) (tyInjN s))
                 *)
                (Hinj : forall n s, P n (tyInj _ s))
                (Hprop : P _ tyProp)
                (Hvar : forall n p, P n (tyVar _ p)).
    Fixpoint mtyp_ind {n} (x : mtyp n) : P n x :=
      match x as x in mtyp n return P n x with
      | tyArr a b => Harr _ _ (mtyp_ind a) (mtyp_ind b)
      (*
      | tyInj0 s => Hinj0 s
      | tyInj1 s => Hinj1 s
      | tyInj2 s => Hinj2 s
      | @tyInjN n s => Hinj n s *)
      | tyInj _ s => Hinj _ s
      | tyApp s ms =>
        Happ _ _ _ (mtyp_ind s) (mtyp_ind ms)
      | tyProp => Hprop
      | tyVar n p => Hvar n p
      end.
  End mtyp_ind.

  Set Elimination Schemes.

  (** Better to match on vector? *)

  Fixpoint default_type_for_arity n : type_for_arity n :=
    match n as n return type_for_arity n with
    | 0 => Empty_set
    | S n => fun _ => default_type_for_arity n
    end.

  Fixpoint mtypD {n} (t : mtyp n) : type_for_arity n :=
    match t in mtyp n return type_for_arity n with
    | tyArr a b => mtypD a -> mtypD b
    (*| tyInj0 s => symbolD s
    | tyInj1 s => symbolD s
    | tyInj2 s => symbolD s
    | tyInjN s => symbolD s
     *)
    | tyInj _ s => symbolD s
    | tyApp s ms => (mtypD s) (mtypD ms)
    | tyProp => Prop
    | tyVar n _ => default_type_for_arity n
    end.

(*
  Let getAppN (a : mtyp 0) : nat :=
    match a with
    | @tyApp n _ _ => n
    | _ => 0
    end.
  Let getApp_f_ms (a : mtyp)
  : option (symbol (3 + getAppN a) * vector mtyp (3 + getAppN a)) :=
    match a as a
          return option (symbol (3 + getAppN a) * vector mtyp (3 + getAppN a))
    with
    | @tyApp n a b => Some (a,b)
    | _ => None
    end.
*)

  Theorem UIP_nat : forall {a b : nat} (pf pf' : a = b), pf = pf'.
  Proof using.
    eapply uip_trans. eapply PeanoNat.Nat.eq_dec.
  Defined.

(*
  Instance Injective_tyApp {n n'} {s : symbol (3+n)} {s' : symbol (3+n')}
           ms ms' : Injective (tyApp s ms = tyApp s' ms') :=
  { result := forall pf : n' = n,
      s = match pf with eq_refl => s' end /\
      ms = match pf with eq_refl => ms' end }.
  Proof.
    intros.
    refine (match H in _ = (@tyApp n' l r)
                  return forall pf : n' = n,
                s = match pf in _ = X return symbol (3 + X) with
                    | eq_refl => l
                    end /\ ms = match pf with
                                | eq_refl => r
                                end
            with
            | eq_refl => fun pf => _
            end pf).
    rewrite (UIP_nat pf eq_refl).
    split; reflexivity.
  Defined.
*)

(*
  Inductive mtypC : Set :=
  | CArr | CApp | CInj0 | CInj1 | CInj2 | CInjN | CProp | CVar.

  Definition ctor {n} (a : mtyp n) : mtypC :=
    match a with
    | tyArr _ _ => CArr
    | tyApp _ _ => CApp
    | tyInj0 _ => CInj0
    | tyInj1 _ => CInj1
    | tyInj2 _ => CInj2
    | tyInjN _ => CInjN
    | tyProp => CProp
    | tyVar _ _ => CVar
    end.

  Definition mtyp_diff_ctor n a : forall (b : mtyp n), ctor a <> ctor b -> a <> b.
    intros.
    intro. apply H. f_equal. assumption.
  Defined.
**)

  Inductive mtypC : Set :=
  | CArr | CApp | CInj | CProp | CVar.

  Definition ctor {n} (a : mtyp n) : mtypC :=
    match a with
    | tyArr _ _ => CArr
    | tyApp _ _ => CApp
(*
    | tyInj0 _ => CInj0
    | tyInj1 _ => CInj1
    | tyInj2 _ => CInj2
    | tyInjN _ => CInjN
*)
    | tyInj _ _ => CInj
    | tyProp => CProp
    | tyVar _ _ => CVar
    end.

  Definition mtyp_diff_ctor n a : forall (b : mtyp n), ctor a <> ctor b -> a <> b.
    intros.
    intro. apply H. f_equal. assumption.
  Defined.

  Lemma tyArr_Inj : forall a b c d, tyArr a b = tyArr c d -> a = c /\ b = d.
  Proof.
    intros.
    refine match H in _ = X
                 return match X with
                        | tyArr c d => a = c /\ b = d
                        | _ => True
                        end
           with
           | eq_refl => conj eq_refl eq_refl
           end.
  Defined.

  Lemma tyApp_Inj : forall n a b c d, @tyApp n a b = tyApp c d -> a = c /\ b = d.
  Proof.
    intros.
    refine (match H in _ = X
                 return match X in mtyp n' return _ with
                        | tyApp c d => fun a b => a = c /\ b = d
                        | _ => fun _ _ => True
                        end a b
           with
           | eq_refl => conj eq_refl eq_refl
           end).
  Defined.

  Lemma tyInj_Inj : forall n s s', tyInj n s = tyInj n s' -> s = s'.
  Proof.
    intros.
    refine (match H in _ = X
                 return match X in mtyp n' return _ with
                        | tyInj c s' => fun s => s = s'
                        | _ => fun _ => True
                        end s
           with
           | eq_refl => eq_refl
           end).
  Defined.

  Lemma tyVar_Inj : forall n s s', tyVar n s = tyVar n s' -> s = s'.
  Proof.
    intros.
    refine (match H in _ = X
                 return match X in mtyp n' return _ with
                        | tyVar c s' => fun s => s = s'
                        | _ => fun _ => True
                        end s
           with
           | eq_refl => eq_refl
           end).
  Defined.

  (** Suppose that we could implement this... *)
  Fixpoint mtyp_dec {n} (a : mtyp n) : forall b, {a = b} + {a <> b}.
  refine
    match a as a in mtyp n
          return forall b : mtyp n, {a = b} + {a <> b}
    with
    | tyArr l r => fun b =>
      match b as b in mtyp n' return {match n' as n' return mtyp n' -> Prop with
                                      | 0 => fun b => tyArr l r = b
                                      | _ => fun _ => False
                                      end b} + {match n' as n' return mtyp n' -> Prop with
                                                | 0 => fun b => not (eq (tyArr l r) b)
                                                | _ => fun _ => True
                                                end b} with
      | tyArr l' r' =>
        match mtyp_dec _ l l'
            , mtyp_dec _ r r'
        with
        | left pf , left pf' => left match pf , pf' with
                                    | eq_refl , eq_refl => eq_refl
                                    end
        | _ , _ => right _
        end
      | _ => right _
      end
    | @tyApp n l r => fun b =>
      match b as b in mtyp n'
            return forall (l : mtyp (S n')) (r : mtyp 0),
                     (forall l', {l = l'} + {l <> l'}) ->
                     (forall r', {r = r'} + {r <> r'}) ->
                     {tyApp l r = b} + {tyApp l r <> b}
      with
      | tyApp l' r' => fun l r recl recr =>
        match recl l' , recr r' with
        | left pf , left pf' => left match pf , pf' with
                                    | eq_refl , eq_refl => eq_refl
                                    end
        | _ , _ => right _
        end
      | _ => fun _ _ _ _ => right _
      end l r (fun x => @mtyp_dec _ l x) (fun x => @mtyp_dec _ r x)
(*
    | tyInj0 s => fun b =>
      match b as b in mtyp 0 return {tyInj0 s = b} + {tyInj0 s <> b}
      with
      | tyInj0 s' => match symbol_dec s s' with
                    | left pf => left match pf with
                                     | eq_refl => eq_refl
                                     end
                    | right _ => right _
                    end
      | _ => _
      end
*)
    | tyInj _ s => fun b =>
      match b as b in mtyp n
            return forall s : symbol n, {tyInj n s = b} + {tyInj n s <> b}
      with
      | tyInj _ s' => fun s =>
        match symbol_dec s s' with
        | left pf => left match pf with
                         | eq_refl => eq_refl
                         end
        | right _ => right _
        end
      | _ => fun _ => right _
      end s
    | tyProp => fun b =>
      match b as b in mtyp n' return {match n' as n' return mtyp n' -> Prop with
                                      | 0 => fun b => tyProp = b
                                      | _ => fun _ => False
                                      end b} + {match n' as n' return mtyp n' -> Prop with
                                      | 0 => fun b => not (tyProp = b)
                                      | _ => fun _ => True
                                      end b} with
      | tyProp => left eq_refl
      | _ => right _
      end
    | tyVar _ p => fun b =>
      match b as b in mtyp n' return {tyVar n' p = b} + {tyVar n' p <> b} with
      | tyVar _ p' =>
        match Pos.eq_dec p p' with
        | left pf => left match pf with
                         | eq_refl => eq_refl
                         end
        | right _ => right _
        end
      | _ => right _
      end
    end.
  all: try solve [ eapply mtyp_diff_ctor; simpl; clear; congruence
                 | destruct n0 ; [ eapply mtyp_diff_ctor; simpl; clear; congruence | trivial ]
                 | intro X; apply tyApp_Inj in X; tauto
                 | intro X; apply tyArr_Inj in X; tauto
                 | intro X; apply tyVar_Inj in X; tauto
                 | intro X; apply tyInj_Inj in X; tauto ].
  Defined.


  Definition mtyp_cast {n} (a b : mtyp n) : option (a = b) :=
    match mtyp_dec a b with
    | left pf => Some pf
    | right _ => None
    end.

(*
  Fixpoint mtyp_cast {n} (a b : mtyp n) : option (a = b).
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
    | tyInj0 s , tyInj0 s' =>
      match symbol_dec s s' with
      | left pf => Some match pf with eq_refl => eq_refl end
      | _ => None
      end
    | tyInj1 s m , tyInj1 s' m' =>
      match symbol_dec s s'
          , mtyp_cast m m'
      with
      | left pf , Some pf' => Some match pf , pf' with
                                   | eq_refl , eq_refl => eq_refl
                                   end
      | _ , _ => None
      end
    | tyInj2 s m m2 , tyInj2 s' m' m2' =>
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
    | tyProp , tyProp => Some eq_refl
    | tyVar a , tyVar b =>
      match Pos.eq_dec a b with
      | left pf => Some (f_equal _ pf)
      | right _ => None
      end
    | _ , _ => None
    end.
  subst. reflexivity.
  Defined.
*)

  Instance RelDec_eq_mtyp {n} : RelDec (@eq (mtyp n)) :=
  { rel_dec := fun a b => if mtyp_dec a b then true else false }.
  Instance RelDec_Correct_eq_mtyp {n} : RelDec_Correct (@RelDec_eq_mtyp n).
  Proof. constructor. unfold rel_dec. simpl.
         intros. destruct (mtyp_dec x y); try tauto.
         split; intros; congruence.
  Defined.



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

  End Pwf.

  Inductive mtyp_acc : forall a b (x : mtyp a) (y : mtyp b), Prop :=
  | tyAcc_tyArrL   : forall x y, mtyp_acc _ _ x (tyArr x y)
  | tyAcc_tyArrR   : forall x y, mtyp_acc _ _ y (tyArr x y)
  | tyAcc_tyAppL   : forall n (x : mtyp (S n)) y, mtyp_acc _ _ x (tyApp x y)
  | tyAcc_tyAppR   : forall n (x : mtyp (S n)) y, mtyp_acc _ _ y (tyApp x y)
  .

  Theorem Pwf_mtyp_acc : @Pwell_founded _ _ mtyp_acc.
  Proof.
    red. induction x; simpl; intros; constructor; inversion 1; auto.
    { subst.
      eapply inj_pair2 in H5.
      subst. auto. }
  Defined.

(* Inductive mtyp_acc (a : mtyp 0) : forall n, mtyp n -> Prop := *)
(*   | tyAcc_tyArrL   : forall b, mtyp_acc a 0 (tyArr a b) *)
(*   | tyAcc_tyArrR   : forall b, mtyp_acc a 0 (tyArr b a) *)
(*   | tyAcc_tyAppL   : forall n b, mtyp_acc a n (tyApp b a) *)
(*   | tyAcc_tyAppR   : forall n b c, mtyp_acc a (S n) b -> mtyp_acc a n (tyApp b c). *)
(* (* *)
(*   | tyAcc_tyInj1  : forall s, mtyp_acc a (tyInj1 s a) *)
(*   | tyAcc_tyInj2L : forall s b, mtyp_acc a (tyInj2 s a b) *)
(*   | tyAcc_tyInj2R : forall s b, mtyp_acc a (tyInj2 s b a) *)
(*   | tyAcc_tyApp    : forall n s ms, vector_In a ms -> mtyp_acc a (@tyApp n s ms). *)
(* *) *)

(*   (* Print well_founded. *) *)
(*   (* Print Acc. *) *)

(*   Theorem wf_mtyp_acc : well_founded (fun a => @mtyp_acc a 0). *)
(*   Proof using. *)
(*     red. *)
(*     generalize dependent 0. *)
(* induction a; constructor; inversion 1; subst; auto. *)
(*     - inv_all. subst. eapply ForallV_vector_In; eauto. *)
(*   Defined. *)

  Instance RType_mtyp : RType (mtyp 0) :=
  { typD := mtypD
  ; type_cast := mtyp_cast
  ; tyAcc := mtyp_acc 0 0 }.

  Local Instance EqDec_symbol : forall n, EqDec (symbol n) (@eq (symbol n)).
  Proof.
    red. intros.
    destruct (symbol_dec x y); (left + right); assumption.
  Defined.

  Local Instance EqDec_mtyp {n} : EqDec (mtyp n) (@eq (mtyp n)).
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

  Lemma symbol_dec_refl
  : forall n (a : symbol n), symbol_dec a a = left eq_refl.
  Proof using.
    intro. apply dec_refl.
  Qed.

  Theorem mtyp_dec_refl : forall n (a : mtyp n), mtyp_dec a a = left eq_refl.
  Proof.
    induction a; simpl.
    - rewrite IHa1; rewrite IHa2; reflexivity.
    - rewrite IHa1; rewrite IHa2; reflexivity.
    - rewrite symbol_dec_refl. reflexivity.
    - reflexivity.
    - rewrite dec_refl. reflexivity.
  Defined.

  Theorem mtyp_cast_refl : forall n (a : mtyp n),
      mtyp_cast a a = Some eq_refl.
  Proof.
    unfold mtyp_cast; intros.
    rewrite mtyp_dec_refl. reflexivity.
  Defined.

  Instance RTypeOk_mtyp : RTypeOk.
  Proof.
    constructor.
    - reflexivity.
    - simpl. eapply Pwell_founded_well_founded. eapply Pwf_mtyp_acc.
    - destruct pf; reflexivity.
    - destruct pf1; destruct pf2; reflexivity.
    - apply mtyp_cast_refl.
    - eauto with typeclass_instances.
  Qed.

  Global Instance Typ0_Prop : Typ0 _ Prop :=
  { typ0 := tyProp
  ; typ0_cast := eq_refl
  ; typ0_match := fun (T : type_for_arity 0 -> Type) (m : mtyp 0) tr =>
    match m as t' in mtyp n'
          return match n' as n' return (type_for_arity 0 -> Type) -> mtyp n' -> Type with
                 | 0 => fun T t' => T (mtypD t')
                 | _ => fun _ _ => unit
                 end T t' ->
                 match n' as n' return (type_for_arity 0 -> Type) -> mtyp n' -> Type with
                 | 0 => fun T t' => T (mtypD t')
                 | _ => fun _ _ => unit
                 end T t'
    with
    | tyProp => fun _ => tr
    | _ => fun fa => fa
    end  }.

  Section elim_mtyp0.
    Variable P : mtyp 0 -> Type.
    Variables (Harr : forall a b, P (tyArr a b))
              (Happ : forall (a : mtyp 1) b, P (tyApp a b))
              (Hprop : P tyProp)
              (Hinj : forall s : symbol 0, P (tyInj 0 s))
              (Hvar : forall p, P (tyVar 0 p)).
    Definition elim_mtyp0 (m : mtyp 0) : P m.
    refine
      match m as m in mtyp 0 return P m with
      | tyArr a b => Harr a b
      | @tyApp n a b => _
      | tyProp => Hprop
      | @tyInj n s => _
      | @tyVar n p => _
      end; destruct n; try solve [ exact idProp ]; eauto.
    Defined.
  End elim_mtyp0.

  Global Instance Typ0Ok_Prop : Typ0Ok Typ0_Prop.
  Proof using.
    constructor.
    { reflexivity. }
    { refine (@elim_mtyp0 _ _ _ _ _ _); simpl; try (right; reflexivity).
      left; exists eq_refl; reflexivity. }
    { destruct pf; reflexivity. }
  Qed.

  Instance Typ0_sym (s : symbol 0) : Typ0 _ (symbolD s) :=
  { typ0 := tyInj 0 s
  ; typ0_cast := eq_refl
  ; typ0_match := fun T (t : mtyp 0) tr =>
    match t as t' in mtyp n'
          return match n' as n' return mtyp n' -> Type with
                 | 0 => fun t' => T (mtypD t')
                 | _ => fun _ => unit
                 end t' ->
                 match n' as n' return mtyp n' -> Type with
                 | 0 => fun t' => T (mtypD t')
                 | _ => fun _ => unit
                 end t'
    with
    | @tyInj 0 s' =>
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
    { refine (@elim_mtyp0 _ _ _ _ _ _); simpl;
        try solve [ right; reflexivity ].
      intros. destruct (symbol_dec s s0); try solve [ right ; eauto ].
      left. subst. exists eq_refl. reflexivity. }
    { destruct pf. reflexivity. }
  Qed.

(*
  Instance Typ1_sym (s : symbol 1) : Typ1 _ (symbolD s) :=
  { typ1 := tyApp (@tyInj 1 s)
  ; typ1_cast := fun _ => eq_refl
  ; typ1_match := fun T (t : mtyp) tr =>
      match t as t return T (mtypD t) -> T (mtypD t) with
      | tyInj1 s' m =>
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
  { typ2 := tyInj2 s
  ; typ2_cast := fun _ _ => eq_refl
  ; typ2_match := fun T (t : mtyp) tr =>
      match t as t return T (mtypD t) -> T (mtypD t) with
      | tyInj2 s' m m' =>
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
*)

  Instance Typ2_Fun : Typ2 _ RFun :=
  { typ2 := tyArr
  ; typ2_cast := fun _ _ => eq_refl
  ; typ2_match := fun T (x : mtyp 0) tr =>
    match x as x in mtyp n'
          return match n' as n' return mtyp n' -> Type with
                 | 0 => fun x => T (mtypD x)
                 | _ => fun _ => unit
                 end x ->
                 match n' as n' return mtyp n' -> Type with
                 | 0 => fun x => T (mtypD x)
                 | _ => fun _ => unit
                 end x
    with
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
    { refine (@elim_mtyp0 _ _ _ _ _ _); try solve [ right ; eauto ].
      simpl. left; do 2 eexists; exists eq_refl; reflexivity. }
    { destruct pf. reflexivity. }
  Qed.

(*
  Global Instance TypeView_sym0
  : PartialView mtyp (symbol 0) :=
  { f_insert := tyInj0;
    f_view :=
     fun x =>
       match x with
       | tyInj0 s => pSome s
       | _ => pNone
       end
  }.

  Definition typ0D := @symbolD _ 0.

  Global Definition TypeViewOk_sym0
  : @TypeViewOk _ _ mtypD typ0D TypeView_sym0.
  Proof.
    constructor; simpl.
    { destruct f; split; try congruence. }
    { reflexivity. }
  Defined.

  Global Instance TypeView_sym1
  : PartialView mtyp (symbol 1 * mtyp) :=
  { f_insert := fun p => tyInj1 (fst p) (snd p);
    f_view :=
     fun x =>
       match x with
       | tyInj1 s t => pSome (s, t)
       | _ => pNone
       end
  }.

  Definition typ1D := (fun ab => @symbolD _ 1 (fst ab) (mtypD (snd ab))).

  Global Definition TypeViewOk_sym1
  : @TypeViewOk _ _ mtypD typ1D TypeView_sym1.
  Proof.
    constructor; simpl.
    { destruct f; split; try congruence.
      { inversion 1. subst. reflexivity. }
      { inversion 1. subst. destruct a; reflexivity. } }
    { reflexivity. }
  Defined.

  Global Instance TypeView_sym2
  : PartialView mtyp (symbol 2 * (mtyp * mtyp)) :=
  { f_insert := fun p => tyInj2 (fst p) (fst (snd p)) (snd (snd p));
    f_view :=
     fun x =>
       match x with
       | tyInj2 s t u => pSome (s, (t, u))
       | _ => pNone
       end
  }.

  Definition typ2D :=
    (fun ab => @symbolD _ 2 (fst ab) (mtypD (fst (snd ab))) (mtypD (snd (snd ab)))).

  Global Definition TypeViewOk_sym2
  : @TypeViewOk _ _ mtypD typ2D TypeView_sym2.
  Proof.
    constructor; simpl.
    { destruct f; split; try congruence.
      { inversion 1. subst. reflexivity. }
      { inversion 1. subst. destruct a; simpl. destruct p. reflexivity. } }
    { reflexivity. }
  Defined.
*)

End parametric.

Arguments tyInj {_} _ _.
Arguments tyApp {_ _} _ _.
Arguments tyArr {_} _ _.
Arguments tyProp {_}.
Arguments tyVar {_} _ _.

Arguments Typ0_sym {_ _} _.
(*
Arguments Typ1_sym {_ _} _.
Arguments Typ2_sym {_ _} _.
*)
Arguments Typ2_Fun {_ _}.
Arguments Typ0Ok_sym {_ _} _.
(*
Arguments Typ1Ok_sym {_ _} _.
Arguments Typ2Ok_sym {_ _} _.
*)
Arguments Typ2Ok_Fun {_ _}.

(*
Arguments TypeView_sym0 {_}.
Arguments TypeView_sym1 {_}.
Arguments TypeView_sym2 {_}.
*)

Arguments symbolD {_ _ _} _.
Arguments symbol_dec {_ _ _} _ _.

(*
Arguments typ0D {_ _} _.
Arguments typ1D {_ _} _.
Arguments typ2D {_ _} _.
*)

(*
Section TSym_sum.
  Variable F G : nat -> Type.
  Context {TSym_F : TSym F} {TSym_G : TSym G}.

  Inductive Fsum (x : nat) : Type :=
  | Finl : F x -> Fsum x
  | Finr : G x -> Fsum x.

  Definition FsumD {n : nat} (fs : Fsum n) : type_for_arity n :=
    match fs with
    | Finl _ x => symbolD x
    | Finr _ x => symbolD x
    end.

  Theorem Finl_inj : forall n x y, Finl n x = Finl n y -> x = y.
  Proof.
    injection 1. tauto.
  Defined.

  Theorem Finr_inj : forall n x y, Finr n x = Finr n y -> x = y.
  Proof.
    injection 1. tauto.
  Defined.

  Theorem Finl_Finr : forall n x y, Finl n x <> Finr n y.
  Proof.
    red. intros. inversion H.
  Defined.

  Definition Fsum_dec {n} (a : Fsum n) : forall b, {a = b} + {a <> b}.
  Proof.
    refine
    match a with
    | Finl _ x => fun b =>
      match b with
      | Finl _ y => match symbol_dec x y with
                    | left pf => left (f_equal _ pf)
                    | right _ => right _
                    end
      | _ => right _
      end
    | Finr _ x => fun b =>
      match b with
      | Finr _ y => match symbol_dec x y with
                    | left pf => left (f_equal _ pf)
                    | right _ => right _
                    end
      | _ => right _
      end
    end.
    intro. apply n0. apply Finl_inj. assumption.
    apply Finl_Finr.
    red. intro. symmetry in H. eapply Finl_Finr. eassumption.
    intro. apply n0. apply Finr_inj. assumption.
  Defined.

  Global Instance TSym_sum : TSym Fsum :=
  { symbolD := @FsumD
  ; symbol_dec := @Fsum_dec }.
End TSym_sum.
*)