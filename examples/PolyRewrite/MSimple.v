(** This is a very simple arithmetic and boolean language that
 ** can be useful for testing.
 **)
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Tactics.
Require Import ExtLib.Data.Map.FMapPositive.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Types.FTypes.
Require Import MirrorCore.Types.TSymOneOf.

Set Implicit Arguments.
Set Strict Implicit.

Inductive typ' : kind -> Set :=
| tyNat : typ' 0
| tyBool : typ' 0.

Definition typ'_dec n (a : typ' n) : forall b : typ' n, {a = b} + {a <> b}.
refine
  match a as a in typ' n return forall b : typ' n, {a = b} + {a <> b} with
  | tyNat => fun b =>
               match b as b in typ' 0 return {tyNat = b} + {tyNat <> b} with
               | tyNat => left eq_refl
               | _ => right _
               end
  | tyBool => fun b =>
               match b as b in typ' 0 return {_ = b} + {_ <> b} with
               | tyBool => left eq_refl
               | _ => right _
               end
  end; try (intro H; inversion H).
Defined.

Instance TSym_typ' : TSym kindD typ' :=
{ symbolD n s :=
    match s with
    | tyNat => nat
    | tyBool => bool
    end
; symbol_dec := typ'_dec }.

Definition typ := ctype typ'.

Global Instance RType_typ : RType typ := RType_type _ _.
Global Instance RTypeOk_typ : @RTypeOk _ RType_typ := RTypeOk_ctyp _ _.

Inductive func :=
| Lt | Plus | N : nat -> func | Eq : typ -> func
| Ex : typ -> func | All : typ -> func
| And | Or | Impl.

Definition func_unify (a b : func) (s : pmap typ) : option (pmap typ) :=
  match a , b with
  | Lt , Lt
  | Plus , Plus
  | N _ , N _
  | And , And
  | Or , Or
  | Impl , Impl => Some s
  | Eq t , Eq t'
  | Ex t , Ex t'
  | All t , All t' =>
    (* danger, this is a hack. but proably ok *)
    match ctype_unify _ 1 t t' s  with
    | Some (s', _) => Some s'
    | _ => None
    end
  | _ , _ => None
  end.

Local Notation "! x" := (@tyBase0 _ x) (at level 0).

Definition typeof_func (f : func) : option typ :=
  Some match f with
       | Lt => tyArr !tyNat (tyArr !tyNat !tyBool)
       | Plus => tyArr !tyNat (tyArr !tyNat !tyNat)
       | N _ => !tyNat
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

Let RelDec_eq_typ : RelDec (@eq typ) := RelDec_Rty _.
Local Existing Instance RelDec_eq_typ.

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
