Require Import Morphisms.
Require Import Relations.
Require Import RelationClasses.
Require Import List Bool.
Require Import ExtLib.Core.Type.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Prop.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.EqDep.
Require Import MirrorCore.TypesI.

Set Implicit Arguments.
Set Strict Implicit.

Section env.
  Fixpoint quant (n : nat) : Type :=
    match n with
      | 0 => Type
      | S n => Type -> quant n
    end.
  Fixpoint qapply (n : nat) (ls : list Type) : quant n -> Type :=
    match n as n , ls return quant n -> Type with
      | 0 , nil => fun t => t
      | S n , l :: ls => fun f => @qapply n ls (f l)
      | _ , _ => fun _ => Empty_set
    end.

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

  Definition types := list type.
(*
  Inductive types : Type :=
  | TEnil : types
  | TEcons : type -> types -> types.
*)

  Variable ts : types.

  (** this type requires decidable equality **)
  Inductive typ : Type :=
  | tyProp
  | tyArr : typ -> typ -> typ
  | tyType : nat -> typ
  | tyVar : nat -> typ.

  Fixpoint typ_eqb (a b : typ) {struct a} : bool :=
    match a , b with
      | tyProp , tyProp => true
      | tyArr a b , tyArr c d =>
        if typ_eqb a c then typ_eqb b d else false
      | tyType x , tyType y => EqNat.beq_nat x y
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
        match nat_eq_odec x y with
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
    { unfold rel_dec in *; simpl in *.
      inversion H.
      consider (EqNat.beq_nat n0 n0); auto. }
    { eapply NPeano.Nat.eqb_eq. inversion H; auto. }
  Qed.

  Theorem nat_eq_odec_None : forall a b, nat_eq_odec a b = None -> a <> b.
  Proof.
    clear; induction a; destruct b; simpl; try congruence.
    specialize (IHa b). destruct (nat_eq_odec a b); try congruence.
    auto.
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
    eapply nat_eq_odec_None in H. congruence.
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
      | tyType x =>
        match nth_error ts x return Type with
          | None => Empty_set
          | Some t => Impl t
        end
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

  Fixpoint subst0_typ (t : typ) (tv : typ) : typ :=
    match tv with
      | tyArr l r => tyArr (subst0_typ t l) (subst0_typ t r)
      | tyVar 0 => t
      | tyVar (S n) => tyVar n
      | tyProp
      | tyType _ => tv
    end.

  Theorem typD_subst0_typ : forall acc t l,
    typD (typD acc l :: acc) t = typD acc (subst0_typ l t).
  Proof.
    induction t; try reflexivity.
    { intros. simpl. rewrite IHt1. rewrite IHt2. reflexivity. }
    { intros. destruct n; simpl; reflexivity. }
  Defined.

  Definition instantiate_typ (ls : list typ) (tv : typ) : typ :=
    List.fold_right subst0_typ tv ls.

  Theorem typD_instantiate_typD_cons : forall c t a b,
    typD (typD b a :: b) (instantiate_typ c t) =
    typD b (instantiate_typ (a :: c) t).
  Proof.
    simpl; intros. rewrite typD_subst0_typ. reflexivity.
  Defined.

  Fixpoint parametric (n : nat) (acc : list Type) (k : list Type -> Type) : Type :=
    match n with
      | 0 => k acc
      | S n => forall T : Type, parametric n (T :: acc) k
    end.

  Fixpoint type_apply n ls acc t {struct n} :
    parametric n acc (fun env => typD env t) ->
    option (typD acc (instantiate_typ ls t)) :=
    match n as n , ls as ls
      return parametric n acc (fun env => typD env t) ->
             option (typD acc (instantiate_typ ls t))
      with
      | 0 , nil => fun X => Some X
      | S n , l :: ls => fun X =>
        match @type_apply n ls _ _ (X (typD acc l)) with
          | None => None
          | Some res =>
            Some match @typD_instantiate_typD_cons _ _ _ _ in _ = t
                   return t with
                   | eq_refl => res
                 end
        end
      | _ , _ => fun _ => None
    end.

  Theorem type_apply_length_equal : forall ft ts' n z fd,
    length ts' = n ->
    exists r, type_apply n ts' z ft fd = Some r.
  Proof.
    induction ts'; simpl in *; intros; subst; simpl; eauto.
    match goal with
      | [ |- exists x, match ?X with _ => _ end = _ ] =>
        consider X
    end; intros; eauto.
    destruct (@IHts' (length ts') (typD z a :: z) (fd (typD z a))
                     eq_refl).
    simpl in *.
    match goal with
      | [ H : ?X = None , H' : ?Y = Some _ |- _ ] =>
        let H'' := fresh in
        assert (H'' : X = Y) by reflexivity; congruence
    end.
  Qed.

  Theorem type_apply_length_equal' : forall ft ts' n z fd r,
    type_apply n ts' z ft fd = Some r ->
    length ts' = n.
  Proof.
    induction ts'; simpl in *; intros; subst; simpl; eauto.
    { destruct n; simpl in *; auto; congruence. }
    { destruct n; simpl in *; try congruence.
      f_equal.
      match goal with
        | [ H : match ?X with _ => _ end = _ |- _ ] =>
          consider X; intros; try congruence
      end.
      inversion H0; clear H0; subst. eauto. }
  Qed.


(*
  Definition const_seqb ts' t t' : typD ts' t -> typD ts' t' -> option bool.
  refine (
    match t as t , t' as t' return typD ts' t -> typD ts' t' -> option bool with
      | tyProp , tyProp => fun _ _ => None
      | tyArr _ _ , tyArr _ _ => fun _ _ => None
      | tyVar t , tyVar t' => fun _ _ => None (** TODO: is this too weak? **)
      | tyType x , tyType y =>
        match nat_eq_odec x y with
          | None => fun _ _ => Some false
          | Some pf =>
            match pf in _ = t
              return match nth_error ts x with
                       | None => Empty_set
                       | Some t => Impl t
                     end ->
                     match nth_error ts t with
                       | None => Empty_set
                       | Some t => Impl t
                     end -> option bool with
              | refl_equal =>
                match nth_error ts x as ty
                  return match ty with
                           | None => Empty_set
                           | Some t => Impl t
                         end ->
                         match ty with
                           | None => Empty_set
                           | Some t => Impl t
                         end -> option bool
                  with
                  | None => fun x _ => match x with end
                  | Some t => @Eqb t
                end
            end
        end
      | _ , _ => fun _ _ => None (** TODO: is this too weak? **)
    end).
  Defined.
*)

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

  Definition typ_cast_typ (F : Type -> Type) (env : list Type) (a b : typ)
  : option (F (typD env a) -> F (typD env b)) :=
    match typ_eq_odec a b with
      | None => None
      | Some pf => Some match pf in _ = t return F (typD env a) -> F (typD env t) with
                          | eq_refl => fun x => x
                        end
    end.

  Theorem typ_cast_typ_eq : forall f ts t t' v,
                              typ_cast_typ f ts t t' = Some v -> t = t'.
  Proof.
    clear. unfold typ_cast_typ; simpl; intros.
    destruct (typ_eq_odec t t'); auto. congruence.
  Qed.

  Theorem typ_cast_typ_refl : forall F env t,
    typ_cast_typ F env t t = Some (fun x => x).
  Proof.
    unfold typ_cast_typ; simpl; intros.
    rewrite typ_eq_odec_Some_refl. reflexivity.
  Qed.

  Definition typ_cast_val ts (a b : typ) (v : typD ts a)
  : option (typD ts b) :=
    match typ_cast_typ (fun x => x) ts a b with
      | None => None
      | Some f => Some (f v)
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
  Require Import ExtLib.Tactics.Injection.

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
    { unfold type_cast. simpl; intros.
      unfold typ_cast_typ in *.
      consider (typ_eq_odec a b); intros; subst.
      inv_all; subst.
      rewrite typ_eq_odec_Some_refl. eauto. congruence. }
    { intros. unfold type_cast; simpl.
      rewrite typ_cast_typ_refl. eauto. }
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
