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
Require Import MirrorCore.Types.FTypes.
Require Import MirrorCore.Types.TSymOneOf.

Set Implicit Arguments.
Set Strict Implicit.

Inductive typ' : kind -> Set :=
| tNat : typ' Kstar
| tBool : typ' Kstar.

Definition typ'_dec n (a : typ' n) : forall b : typ' n, {a = b} + {a <> b}.
refine
  match a as a in typ' n return forall b : typ' n, {a = b} + {a <> b} with
  | tNat => fun b =>
               match b as b in typ' 0 return {tNat = b} + {tNat <> b} with
               | tNat => left eq_refl
               | _ => right _
               end
  | tBool => fun b =>
               match b as b in typ' 0 return {_ = b} + {_ <> b} with
               | tBool => left eq_refl
               | _ => right _
               end
  end; try (intro H; inversion H).
Defined.

Instance TSym_typ' : TSym kindD typ' :=
{ symbolD n s :=
    match s with
    | tNat => nat
    | tBool => bool
    end
; symbol_dec := typ'_dec }.

Definition typ := ctyp typ' Kstar.

Global Instance RType_typ : RType typ := _.
Global Instance RTypeOk_typ : @RTypeOk _ RType_typ := _.

(*
Global Instance RelDec_typ : RelDec (@eq typ) := RelDec_eq_ctyp typ' TSym_typ'.
Global Instance RelDec_Correct_typ : RelDec_Correct RelDec_typ := RelDec_Correct_eq_ctyp typ' TSym_typ'.
*)

Definition tyNat := tyBase0 tNat.
Definition tyBool := tyBase0 tBool.

Definition tyProp := @tyProp typ'.

Global Instance Typ2_tyArr : Typ2 RType_typ Fun := _.
Global Instance Typ2Ok_tyArr : Typ2Ok Typ2_tyArr := _.

Global Instance Typ0_tyProp : Typ0 RType_typ Prop := _.
Global Instance Typ0Ok_tyProp : Typ0Ok Typ0_tyProp := _.

Global Instance Typ0_tyNat : Typ0 RType_typ nat := Typ0_sym tNat.
Global Instance Typ0Ok_tyNat : Typ0Ok Typ0_tyNat := Typ0Ok_sym tNat.

Global Instance Typ0_tyBool : Typ0 RType_typ bool := Typ0_sym tBool.
Global Instance Typ0Ok_tyBool : Typ0Ok Typ0_tyBool := Typ0Ok_sym tBool.
