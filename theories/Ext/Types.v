Require Import Morphisms.
Require Import Relations.
Require Import RelationClasses.
Require Import List Bool.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Prop.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.
Require Import ExtLib.Tactics.EqDep.
Require Import MirrorCore.TypesI.

Set Implicit Arguments.
Set Strict Implicit.

Section env.
  (** Syntax **)
  Record type : Type := Typ {
    Impl : Type ;
    Eqb : Impl -> Impl -> option bool ;
    Eqb_correct : forall a b : Impl,
      match Eqb a b with
        | None => True
        | Some true => a = b
        | Some false => a <> b
      end
  }.

  Definition default_type (T : Type) : type.
  refine (
    {| Impl := T
     ; Eqb := fun _ _ => None
    |}); abstract auto.
  Defined.

  Definition empty_type : type :=
    {| Impl := Empty_set
     ; Eqb := fun x _ => match x with end
     ; Eqb_correct := fun x => match x with end
    |}.

  Inductive types : Type :=
  | TEemp : types
  | TEbranch : types -> option Type -> types -> types.

  Definition types_left (t : types) : types :=
    match t with
      | TEemp => TEemp
      | TEbranch l _ _ => l
    end.

  Definition types_right (t : types) : types :=
    match t with
      | TEemp => TEemp
      | TEbranch l _ _ => l
    end.

  Definition types_here (t : types) : option Type :=
    match t with
      | TEemp => None
      | TEbranch _ v _ => v
    end.

  Fixpoint types_add (n : positive) (v : Type) (t : types) : types :=
    match n with
      | xH => TEbranch (types_left t) (Some v) (types_right t)
      | xI n => TEbranch (types_left t) (types_here t) (types_add n v (types_right t))
      | xO n => TEbranch (types_add n v (types_left t)) (types_here t) (types_right t)
    end.

  Fixpoint list_to_types' (ls : list (option Type)) (n : positive)
  : types -> types :=
    match ls with
      | nil => fun x => x
      | None :: ls => list_to_types' ls (Pos.succ n)
      | Some v :: ls => fun ts =>
                          list_to_types' ls (Pos.succ n) (types_add n v ts)
    end.

  Definition list_to_types (ls : list (option Type)) : types :=
    list_to_types' ls 1%positive TEemp.

  Fixpoint getType (ts : types) (n : positive) {struct n} : Type :=
    match n with
      | xH => match ts with
                | TEbranch _ (Some T) _ => T
                | _ => Empty_set
              end
      | xO n => getType (types_left ts) n
      | xI n => getType (types_right ts) n
    end.

  Variable ts : types.

  (** this type requires decidable equality **)
  Inductive typ : Type :=
  | tyProp
  | tyArr : typ -> typ -> typ
  | tyType : positive -> typ
  | tyVar : nat -> typ.

  Fixpoint typ_eqb (a b : typ) {struct a} : bool :=
    match a , b with
      | tyProp , tyProp => true
      | tyArr a b , tyArr c d =>
        if typ_eqb a c then typ_eqb b d else false
      | tyType x , tyType y => x ?[ eq ] y
      | tyVar x , tyVar y => EqNat.beq_nat x y
      | _ , _ => false
    end.

  Fixpoint nat_eq_odec (a b : nat) : option (a = b) :=
    match a as a , b as b return option (a = b) with
      | 0 , 0 => Some (eq_refl _)
      | S a , S b => match nat_eq_odec a b with
                       | None => None
                       | Some pf => Some (match pf in _ = b' return S a = S b' with
                                            | eq_refl => eq_refl
                                          end)
                     end
      | _ , _ => None
    end.

  Fixpoint positive_eq_odec (a b : positive) : option (a = b) :=
    match a as a , b as b return option (a = b) with
      | xH , xH => Some (eq_refl _)
      | xI a , xI b =>
        match positive_eq_odec a b with
          | None => None
          | Some pf => Some (match pf in _ = b' return xI a = xI b' with
                               | eq_refl => eq_refl
                             end)
        end
      | xO a , xO b =>
        match positive_eq_odec a b with
          | None => None
          | Some pf => Some (match pf in _ = b' return xO a = xO b' with
                               | eq_refl => eq_refl
                             end)
        end
      | _ , _ => None
    end.

  Fixpoint typ_eq_odec (a b : typ) : option (a = b) :=
    match a as a , b as b return option (a = b) with
      | tyProp , tyProp => Some (eq_refl _)
      | tyArr a b , tyArr c d =>
        match typ_eq_odec a c with
          | None => None
          | Some pf => match typ_eq_odec b d with
                         | None => None
                         | Some pf' =>
                           Some match pf in _ = a' , pf' in _ = b'
                                  return tyArr a b = tyArr a' b' with
                                  | eq_refl , eq_refl => eq_refl _
                                end
                       end
        end
      | tyType x , tyType y =>
        match positive_eq_odec x y with
          | None => None
          | Some pf => Some (match pf in _ = y' return tyType x = tyType y' with
                               | eq_refl => eq_refl
                             end)
        end
      | tyVar x , tyVar y =>
        match nat_eq_odec x y with
          | None => None
          | Some pf => Some (match pf in _ = y' return tyVar x = tyVar y' with
                               | eq_refl => eq_refl
                             end)
        end
      | _ , _ => None
    end.

  Global Instance RelDec_eq_typ : RelDec (@eq typ) :=
  { rel_dec := typ_eqb }.

  Theorem typ_eqb_true : forall a b, typ_eqb a b = true -> a = b.
  Proof.
    induction a; destruct b; simpl; intros;
      try solve [ congruence | f_equal; apply EqNat.beq_nat_true; assumption ].
    { consider (typ_eqb a1 b1); intros. f_equal; auto. }
    { consider (p ?[ eq ] p0); intros. f_equal; auto. }
  Defined.

  Global Instance RelDecOk_eq_typ : RelDec_Correct RelDec_eq_typ.
  Proof.
    constructor.
    induction x; destruct y; simpl; intuition;
      try solve [ congruence | f_equal; apply EqNat.beq_nat_true; assumption ].
    { consider (typ_eqb x1 y1); intros.
      rewrite IHx1 in H. rewrite IHx2 in H0. subst; reflexivity. }
    { inversion H. apply IHx1 in H1. apply IHx2 in H2.
      simpl in *. inversion H; subst. unfold rel_dec in *; simpl in *. rewrite H1. auto. }
    { consider (p ?[ eq ] p0); intros; f_equal; auto. }
    { inversion H. consider (p0 ?[ eq ] p0); auto. }
    { eapply NPeano.Nat.eqb_eq. inversion H; auto. }
  Qed.

  Theorem nat_eq_odec_None : forall a b, nat_eq_odec a b = None -> a <> b.
  Proof.
    clear; induction a; destruct b; simpl; try congruence.
    specialize (IHa b). destruct (nat_eq_odec a b); try congruence.
    auto.
  Qed.

  Theorem positive_eq_odec_None : forall a b, positive_eq_odec a b = None -> a <> b.
  Proof.
    clear; induction a; destruct b; simpl; try congruence.
    { specialize (IHa b).
      destruct (positive_eq_odec a b); intros; try congruence.
      specialize (IHa eq_refl). congruence. }
    { specialize (IHa b).
      destruct (positive_eq_odec a b); intros; try congruence.
      specialize (IHa eq_refl). congruence. }
  Qed.

  Theorem typ_eq_odec_None : forall t t',
    typ_eq_odec t t' = None -> t <> t'.
  Proof.
    induction t; destruct t'; simpl in *; try congruence; intros;
      repeat match goal with
               | [ H : match ?X with _ => _ end = _ |- _ ] =>
                 consider X; intros; subst; try congruence
             end.
    eapply IHt2 in H0; congruence.
    eapply IHt1 in H; congruence.
    eapply positive_eq_odec_None in H. congruence.
    eapply nat_eq_odec_None in H. congruence.
  Qed.

  Global Instance EqDec_typ : EquivDec.EqDec _ (@eq typ).
  Proof.
    red. intros. consider (x ?[ eq ] y); intuition.
  Qed.

  Theorem typ_eq_odec_None_refl : forall t,
    typ_eq_odec t t = None -> False.
  Proof.
    intros. apply typ_eq_odec_None in H. auto.
  Qed.

  Theorem typ_eq_odec_Some_refl : forall t,
    typ_eq_odec t t = Some refl_equal.
  Proof.
    intros. consider (typ_eq_odec t t); intros; auto.
    { f_equal. uip_all. reflexivity. }
    { exfalso; eauto using typ_eq_odec_None_refl. }
  Qed.

  Fixpoint typD (env : list Type) (x : typ) {struct x} : Type :=
    match x return Type with
      | tyProp => Prop
      | tyArr l r => typD env l -> typD env r
      | tyType x => getType ts x
      | tyVar x =>
        match nth_error env x return Type with
          | None => Empty_set
          | Some t => t
        end
    end.

  Definition type_of_apply (tv x : typ) : option typ :=
    match tv with
      | tyArr l r =>
        if typ_eqb l x then Some r else None
      | _ => None
    end.

  Fixpoint equiv (t : typ) : forall a b : typD nil t, Prop :=
    match t as t return typD nil t -> typD nil t -> Prop with
      | tyArr a b => fun x y => forall a, equiv b (x a) (y a)
      | tyProp => fun x y => x <-> y
      | tyVar i => fun x y => x = y
      | tyType i => fun x y => x = y
    end.

  Global Instance Reflexive_equiv t : Reflexive (equiv t).
  Proof.
    induction t; simpl; intuition.
  Qed.
  Global Instance Symmetric_equiv t : Symmetric (equiv t).
  Proof.
    induction t; simpl; intuition.
  Qed.
  Global Instance Transitive_equiv t : Transitive (equiv t).
  Proof.
    induction t; red; simpl; intuition; etransitivity; eauto.
  Qed.

  Definition typ_cast_typ (env : list Type) (a b : typ)
  : option (forall F, F (typD env a) -> F (typD env b)) :=
    match typ_eq_odec a b with
      | None => None
      | Some pf => Some (fun F =>
                           match pf in _ = t return F (typD env a) -> F (typD env t) with
                             | eq_refl => fun x => x
                           end)
    end.

  Theorem typ_cast_typ_refl : forall env t,
                                typ_cast_typ env t t = Some (fun F x => x).
  Proof.
    unfold typ_cast_typ; simpl; intros.
    rewrite typ_eq_odec_Some_refl. reflexivity.
  Qed.

  (** NOTE: These requirements are pretty strict, they say
   ** precisely that typ_cast_typ implies equality. For the time
   ** being that is ok.
   **)
  Theorem typ_cast_typ_eq : forall ts t t' v,
                              typ_cast_typ ts t t' = Some v -> t = t'.
  Proof.
    clear. unfold typ_cast_typ; simpl; intros.
    destruct (typ_eq_odec t t'); auto. congruence.
  Qed.

  Lemma typ_cast_typ_neq : forall env t t',
                             t <> t' ->
                             typ_cast_typ env t t' = None.
  Proof.
    intros.
    consider (typ_cast_typ env t t'); auto; intros.
    exfalso. generalize (typ_cast_typ_eq _ _ _ H0). auto.
  Qed.

  Lemma typ_cast_typ_neq' : forall env t t',
                              typ_cast_typ env t t' = None ->
                              t <> t'.
  Proof.
    intros. unfold typ_cast_typ in *.
    consider (typ_eq_odec t t'); intros; try congruence.
    eapply typ_eq_odec_None in H. auto.
  Qed.

  Definition typ_cast_val ts (a b : typ) (v : typD ts a)
  : option (typD ts b) :=
    match typ_cast_typ ts a b with
      | None => None
      | Some f => Some (f (fun x => x) v)
    end.

  Lemma typ_cast_val_eq : forall ts a b v v',
                            typ_cast_val ts a b v = Some v' ->
                            a = b.
  Proof.
    clear. unfold typ_cast_val; simpl; intros.
    unfold typ_cast_typ in *. generalize (@typ_eq_odec_None a b).
    destruct (typ_eq_odec a b); auto. congruence.
  Qed.

  Lemma typ_cast_val_refl : forall ts t v,
    typ_cast_val ts t t v = None -> False.
  Proof.
    unfold typ_cast_val, typ_cast_typ.
    intros. rewrite typ_eq_odec_Some_refl in H. congruence.
  Qed.

  Require Import ExtLib.Core.Type.

  Fixpoint typ_typeFor g t : type (typD g t) :=
    match t as t return type (typD g t) with
      | tyProp => type_Prop
      | tyArr l r => type_Fun (typ_typeFor g l) (typ_typeFor g r)
      (** These don't work perfectly because when you make something
                         a var, it potentially changes its type **)
      | tyType i => type_libniz _ (** TODO: This should be a lookup **)
      | tyVar v => type_libniz _ (** TODO: This should be a lookup **)
    end.

  Global Instance RType_typ : RType typD :=
  { type_cast := typ_cast_typ
  ; type_eqb := _
  ; typeFor := typ_typeFor
(*
  ; instantiate_typ := instantiate_typ
  ; type_of_apply := type_of_apply
*)
  }.

  Global Instance RTypeOk_typ : RTypeOk RType_typ.
  Proof.
    constructor.
    eauto with typeclass_instances.
    { intros. unfold type_cast; simpl.
      rewrite typ_cast_typ_refl. eauto. }
    { unfold type_cast. simpl; intros.
      unfold typ_cast_typ in *.
      consider (typ_eq_odec a b); intros; subst.
      inv_all; subst.
      rewrite typ_eq_odec_Some_refl. eauto. congruence. }
    { unfold type_cast, typ_cast_typ; simpl.
      unfold type_cast, typ_cast_typ; simpl.
      intros.
      forward.
      subst.
      inv_all; subst.
      rewrite H. eexists; split; eauto. }
  Qed.

  Global Instance TypInstance0_tyProp : TypInstance0 typD Prop :=
  { typ0 := tyProp
  ; typ0_iso := fun ts => Iso.Equiv_ident _
  ; typ0_match := fun _ _ caseType caseElse t =>
                    match t with
                      | tyProp => caseType tt
                      | x => caseElse x
                    end
  }.

  Global Instance TypInstance2_tyArr : TypInstance2 typD Fun :=
  { typ2 := tyArr
  ; typ2_iso := fun ts t1 t2 => Iso.Equiv_ident _
  ; typ2_match := fun _ t _ caseType caseElse =>
                    match t with
                      | tyArr l r => caseType l r
                      | x => caseElse x
                    end
  ; typ2_matchW := fun ts t R caseType caseElse =>
                    match t as t' return (unit -> R (typD ts t')) -> R (typD ts t') with
                      | tyArr l r => fun _ => caseType l r
                      | x => fun caseElse => caseElse tt
                    end caseElse
  }.

End env.
