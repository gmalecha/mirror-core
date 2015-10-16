(** This is a very simple arithmetic and boolean language that
 ** can be useful for testing.
 **)
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Lambda.ExprCore.

Set Implicit Arguments.
Set Strict Implicit.

Inductive typ :=
| tyArr : typ -> typ -> typ
| tyNat | tyBool
| tyProp.

Fixpoint typD (t : typ) : Type :=
  match t with
    | tyNat => nat
    | tyBool => bool
    | tyProp => Prop
    | tyArr a b => typD a -> typD b
  end.

Definition typ_eq_dec : forall a b : typ, {a = b} + {a <> b}.
  decide equality.
Defined.

Instance RelDec_eq_typ : RelDec (@eq typ) :=
{ rel_dec := fun a b =>
               match typ_eq_dec a b with
                 | left _ => true
                 | right _ => false
               end }.

Instance RelDec_Correct_eq_typ : RelDec_Correct RelDec_eq_typ.
Proof.
  constructor.
  intros.
  unfold rel_dec; simpl.
  destruct (typ_eq_dec x y); intuition.
Qed.

Inductive tyAcc' : typ -> typ -> Prop :=
| tyArrL : forall a b, tyAcc' a (tyArr a b)
| tyArrR : forall a b, tyAcc' b (tyArr a b).

Instance RType_typ : RType typ :=
{ typD := typD
; tyAcc := tyAcc'
; type_cast := fun a b => match typ_eq_dec a b with
                            | left pf => Some pf
                            | _ => None
                          end
}.

Instance RTypeOk_typ : @RTypeOk typ _.
Proof.
  eapply makeRTypeOk.
  { red.
    induction a; constructor; inversion 1.
    subst; auto.
    subst; auto. }
  { unfold type_cast; simpl.
    intros. destruct (typ_eq_dec x x).
    f_equal. compute.
    uip_all. reflexivity. congruence. }
  { unfold type_cast; simpl.
    intros. destruct (typ_eq_dec x y); try congruence. }
Qed.

Instance Typ2_tyArr : Typ2 _ Fun :=
{ typ2 := tyArr
; typ2_cast := fun _ _ => eq_refl
; typ2_match :=
    fun T t tr =>
      match t as t return T (TypesI.typD t) -> T (TypesI.typD t) with
        | tyArr a b => fun _ => tr a b
        | _ => fun fa => fa
      end
}.

Instance Typ2Ok_tyArr : Typ2Ok Typ2_tyArr.
Proof.
  constructor.
  { reflexivity. }
  { apply tyArrL. }
  { intros; apply tyArrR. }
  { inversion 1; subst; unfold Rty; auto. }
  { destruct x; simpl; eauto.
    left; do 2 eexists; exists eq_refl. reflexivity. }
  { destruct pf. reflexivity. }
Qed.

Instance Typ0_tyProp : Typ0 _ Prop :=
{| typ0 := tyProp
 ; typ0_cast := eq_refl
 ; typ0_match := fun T t =>
                   match t as t
                         return T Prop -> T (TypesI.typD t) -> T (TypesI.typD t)
                   with
                     | tyProp => fun tr _ => tr
                     | _ => fun _ fa => fa
                   end
 |}.

Inductive func :=
| Lt | Plus | N : nat -> func | Eq : typ -> func
| Ex : typ -> func | All : typ -> func
| And | Or | Impl.

Definition typeof_func (f : func) : option typ :=
  Some match f with
         | Lt => tyArr tyNat (tyArr tyNat tyBool)
         | Plus => tyArr tyNat (tyArr tyNat tyNat)
         | N _ => tyNat
         | Eq t => tyArr t (tyArr t tyProp)
         | And | Or | Impl => tyArr tyProp (tyArr tyProp tyProp)
         | Ex t | All t => tyArr (tyArr t tyProp) tyProp
       end.

Definition funcD (f : func)
: match typeof_func f with
    | None => unit
    | Some t => typD t
  end :=
  match f as f return match typeof_func f with
                        | None => unit
                        | Some t => typD t
                      end
  with
    | Lt => NPeano.Nat.ltb
    | Plus => plus
    | N n => n
    | Eq t => @eq _
    | And => and
    | Or => or
    | Impl => fun (P Q : Prop) => P -> Q
    | All t => fun P => forall x : typD t, P x
    | Ex t => fun P => exists x : typD t, P x
  end.

Instance RelDec_eq_func : RelDec (@eq func) :=
{ rel_dec := fun (a b : func) =>
               match a , b with
                 | Plus , Plus => true
                 | Lt , Lt => true
                 | N a , N b => a ?[ eq ] b
                 | Eq a , Eq b => a ?[ eq ] b
                 | And , And
                 | Impl , Impl
                 | Or , Or => true
                 | All a , All b
                 | Ex a , Ex b => a ?[ eq ] b
                 | _ , _ => false
               end
}.

Instance RelDecCorrect_eq_func : RelDec_Correct RelDec_eq_func.
Proof.
  constructor.
  destruct x; destruct y; simpl;
  try solve [ tauto
            | split; congruence
            | rewrite rel_dec_correct; split; congruence
            ].
Qed.

Instance RSym_func : RSym func :=
{ typeof_sym := typeof_func
; symD := funcD
; sym_eqb := fun a b => Some (a ?[ eq ] b)
}.

Instance RSymOk_func : RSymOk RSym_func.
{ constructor.
  intros. simpl. consider (a ?[ eq ] b); auto. }
Qed.