Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require MirrorCore.syms.SymEnv.
Require MirrorCore.syms.SymSum.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Simple.
Require Import MirrorCore.Reify.Reify.

Require Import McExamples.Cancel.Monoid.

Set Implicit Arguments.
Set Strict Implicit.

Module Syntax (M : Monoid).

  (** Define the reified language *)
  (********************************)

  (* The syntax of types *)
  Inductive typ :=
  | tyArr : typ -> typ -> typ
  | tyNat | tyM
  | tyProp.

  (* The meaning of types *)
  Fixpoint typD (t : typ) : Type :=
    match t with
    | tyNat => nat
    | tyM => M.M
    | tyProp => Prop
    | tyArr a b => typD a -> typD b
    end.

  (* The accessibility relation *)
  Inductive tyAcc' : typ -> typ -> Prop :=
  | tyArrL : forall a b, tyAcc' a (tyArr a b)
  | tyArrR : forall a b, tyAcc' b (tyArr a b).

  Fixpoint typ_eq_odec (a b : typ) : option (a = b) :=
    match a , b with
    | tyNat , tyNat
    | tyM , tyM
    | tyProp , tyProp => Some eq_refl
    | tyArr a b , tyArr a' b' =>
      match typ_eq_odec a a'
          , typ_eq_odec b b'
      with
      | Some pf , Some pf' => Some match pf , pf' with
                                   | eq_refl , eq_refl => eq_refl
                                   end
      | _ , _ => None
      end
    | _ , _ => None
    end.

  Fixpoint typ_eqb (a b : typ) : bool :=
    match a , b with
    | tyNat , tyNat
    | tyM , tyM
    | tyProp , tyProp => true
    | tyArr a b , tyArr a' b' =>
      typ_eqb a a' && typ_eqb b b'
    | _ , _ => false
    end.

  (* Instantiate the RType interface *)
  Instance RType_typ : RType typ :=
  { typD := typD
  ; tyAcc := tyAcc'
  ; type_cast := typ_eq_odec }.
  Instance RTypeOk_typ : RTypeOk.
  Proof.
    constructor; try reflexivity.
    - prove_simple_acc.
    - destruct pf; reflexivity.
    - destruct pf1; destruct pf2; reflexivity.
    - induction x; simpl; try reflexivity.
      + change_rewrite IHx1.
        change_rewrite IHx2. reflexivity.
    - red. unfold equiv. unfold complement.
      intros; change (x = y -> False) with (not (x = y)).
      decide equality.
  Defined.

  (* Build instances for describing functions and Prop *)
  Instance Typ2_tyArr : Typ2 RType_typ Fun :=
  { typ2 := tyArr
  ; typ2_cast := fun _ _ => eq_refl
  ; typ2_match T t tr :=
      match t as t return T (typD t) -> T (typD t) with
      | tyArr a b => fun _ => tr a b
      | _ => fun fa => fa
      end }.

  Instance Typ2Ok_tyArr : Typ2Ok Typ2_tyArr.
  Proof. prove_TypOk. Defined.

  Instance Typ0_tyProp : Typ0 RType_typ Prop :=
  { typ0 := tyProp
  ; typ0_cast := eq_refl
  ; typ0_match T t :=
      match t with
      | tyProp => fun tr _ => tr
      | _ => fun _ fa => fa
      end }.

  Instance Typ0Ok_tyProp : Typ0Ok Typ0_tyProp.
  Proof. prove_TypOk. Defined.

  (* The syntax of terms *)
  Inductive func' :=
  | Eq : typ -> func' (* polymorphic equality *)
  | Ex : typ -> func' | All : typ -> func' (* polymorphic quantification *)
  | And | Or | Impl
  | mU | mP | mR.

  Fixpoint func'_eqb (a b : func') : bool :=
    match a , b with
    | And , And
    | Or , Or
    | Impl , Impl
    | mU , mU
    | mP , mP
    | mR , mR => true
    | Eq t , Eq t'
    | Ex t , Ex t'
    | All t , All t' => typ_eqb t t'
    | _ , _ => false
    end.

  Definition typeof_func' (f : func') : option typ :=
    Some match f with
         | mU => tyM
         | mP => tyArr tyM (tyArr tyM tyM)
         | mR => tyArr tyM (tyArr tyM tyProp)
         | Eq t => tyArr t (tyArr t tyProp)
         | And | Or | Impl => tyArr tyProp (tyArr tyProp tyProp)
         | Ex t | All t => tyArr (tyArr t tyProp) tyProp
         end.

  Definition func'D (f : func')
  : match typeof_func' f with
    | None => unit
    | Some t => typD t
    end :=
    match f as f return match typeof_func' f with
                        | None => unit
                        | Some t => typD t
                        end
    with
    | mU => M.U
    | mP => M.P
    | mR => M.R
    | Eq t => @eq _
    | And => and
    | Or => or
    | Impl => fun (P Q : Prop) => P -> Q
    | All t => fun P => forall x : typD t, P x
    | Ex t => fun P => exists x : typD t, P x
    end.

  Instance RelDec_func'_eq : RelDec (@eq func') :=
  { rel_dec := fun (a b : func') =>
                 match a , b with
                 | mU , mU => true
                 | mP , mP => true
                 | mR , mR => true
                 | Eq a , Eq b => a ?[ eq ] b
                 | And , And
                 | Impl , Impl
                 | Or , Or => true
                 | All a , All b
                 | Ex a , Ex b => a ?[ eq ] b
                 | _ , _ => false
                 end
  }.

  (* The meaning of symbols *)
  Definition RSym_func' : RSym func' :=
  {| typeof_sym := typeof_func'
  ; symD := func'D
  ; sym_eqb := fun a b => Some (a ?[ eq ] b) |}.

  Instance RelDec_Correct_typ : @RelDec_Correct _ (@eq typ) _.
  Proof.
    constructor.
    induction x; destruct y; simpl in *;
    try solve [ split; first [ tauto | congruence ] ].
    specialize (IHx1 y1). specialize (IHx2 y2).
    unfold rel_dec in *. simpl in *.
    destruct (typ_eq_odec x1 y1).
    + destruct (typ_eq_odec x2 y2).
      - split; try tauto. intros. f_equal; eauto.
      - split. intros; f_equal; eauto.
        eapply IHx2; eauto.
        inversion 1. tauto.
    + split. inversion 1.
      intros. apply IHx1. congruence.
  Qed.

  Instance RSymOk_func' : RSymOk RSym_func'.
  Proof.
    constructor.
    destruct a; destruct b; simpl; try congruence.
    - consider (t ?[ eq ] t0); intros; subst; congruence.
    - consider (t ?[ eq ] t0); intros; subst; congruence.
    - consider (t ?[ eq ] t0); intros; subst; congruence.
  Qed.

  Definition func : Type := sum func' SymEnv.func.

  Instance RSym_func fs : RSym func :=
    SymSum.RSym_sum RSym_func' (@SymEnv.RSym_func _ _ fs).

  Instance RSymOk_func fs : RSymOk (RSym_func fs).
  Proof.
    apply SymSum.RSymOk_sum; eauto with typeclass_instances.
  Qed.

  Definition known (f : func') : expr typ func := Inj (inl f).
  Definition other (f : SymEnv.func) : expr typ func := Inj (inr f).

  (** Reification **)
  (*****************)

  Local Notation "x @ y" := (@RApp x y) (only parsing, at level 30).
  Local Notation "'!!' x" := (@RExact _ x) (only parsing, at level 25).
  Local Notation "'?' n" := (@RGet n RIgnore) (only parsing, at level 25).
  Local Notation "'?!' n" := (@RGet n RConst) (only parsing, at level 25).
  Local Notation "'#'" := RIgnore (only parsing, at level 0).

  (* Declare patterns **)
  Reify Declare Patterns patterns_monoid_typ : typ.
  Reify Declare Patterns patterns_monoid : expr typ func.

  (* Declare the syntax for the types *)
  Reify Declare Syntax reify_monoid_typ :=
    Patterns.CPatterns patterns_monoid_typ.

  Reify Declare Typed Table table_terms : BinNums.positive => typ.

  (* Declare syntax **)
  Reify Declare Syntax reify_monoid :=
    Patterns.CFirst ((Patterns.CPatterns patterns_monoid) ::
                     (Patterns.CApp (@ExprCore.App typ func)) ::
                     (Patterns.CAbs reify_monoid_typ (@ExprCore.Abs typ func)) ::
                     (Patterns.CVar (@ExprCore.Var typ func)) ::
                     (Patterns.CMap other (Patterns.CTypedTable reify_monoid_typ table_terms)) :: nil).

  (* Pattern rules for reifying types *)
  Reify Pattern patterns_monoid_typ += (@RExact _ nat)  => tyNat.
  Reify Pattern patterns_monoid_typ += (@RExact _ M.M) => tyM.
  Reify Pattern patterns_monoid_typ += (@RExact _ Prop) => tyProp.
  Reify Pattern patterns_monoid_typ += (@RImpl (@RGet 0 RIgnore) (@RGet 1 RIgnore)) => (fun (a b : function reify_monoid_typ) => tyArr a b).

  (* Pattern rules for reifying terms *)
  Reify Pattern patterns_monoid += (@RExact _ M.P) => (known mP).
  Reify Pattern patterns_monoid += (@RExact _ M.U) => (known mU).
  Reify Pattern patterns_monoid += (@RExact _ M.R) => (known mR).
  Reify Pattern patterns_monoid += (RApp (@RExact _ (@eq)) (RGet 0 RIgnore)) =>
  (fun (t : function reify_monoid_typ) => Inj (typ:=typ) (Eq t)).
  Reify Pattern patterns_monoid += (RPi (RGet 0 RIgnore) (RGet 1 RIgnore)) => (fun (t : function reify_monoid_typ) (b : function reify_monoid) => (App (known (All t)) (Abs t b))).
  Reify Pattern patterns_monoid += (@RImpl (@RGet 0 RIgnore) (@RGet 1 RIgnore)) => (fun (a b : function reify_monoid) => App (App (known Impl) a) b).


End Syntax.