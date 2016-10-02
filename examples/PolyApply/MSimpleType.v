(** This is a very simple arithmetic and boolean language that
 ** can be useful for testing.
 **)
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.PList.
Require Import ExtLib.Tactics.

Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.MTypes.ModularTypes.
Require Import MirrorCore.MTypes.TSymOneOf.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.MTypes.ListType.
Require Import MirrorCore.MTypes.BaseType.
Require Import MirrorCore.Views.ViewSumN.
Require Import MirrorCore.Reify.ReifyClass.
Require Import MirrorCore.Reify.ReifyView.

Set Implicit Arguments.
Set Strict Implicit.

Import OneOfType.

Definition typ_map := 
  list_to_pmap
    (pcons base_typ
           (pcons list_typ
                  pnil)).

Definition typ' := OneOfF typ_map.

Definition typ := mtyp typ'.

Ltac pmap_lookup'_simpl :=
  repeat (
    match goal with 
    | H : match pmap_lookup' Empty ?p with | _Some _ => _ | _None => Empty_set end |- _ => 
      exfalso; clear -H; rewrite pmap_lookup'_Empty in H; destruct H
    | H : match pmap_lookup' _ ?p with | _Some _ => _ | _None => Empty_set end |- _ => 
      destruct p; simpl in H
    end).

Ltac eq_dec_right :=
  let H := fresh "H" in
    right; intro H; inv_all; congruence.

Definition typ'_dec {n} (a : typ' n) : forall b, {a = b} + {a <> b}.
Proof.
  intros.
  destruct a as [a1 v1].
  destruct b as [a2 v2].
  unfold typ_map, list_to_pmap, type_nth in *; simpl in *.
  pmap_lookup'_simpl; try eq_dec_right.  
  pose proof (list_typ_dec v1 v2).
  destruct H; [left; subst; reflexivity|].
  right; intros H; apply n0; inv_all; subst.
  assert (x = eq_refl) by (apply UIP_refl); subst. reflexivity.
  pose proof (base_typ_dec v1 v2).
  destruct H; [left; subst; reflexivity|].
  right; intros H; apply n0; inv_all; subst.
  assert (x = eq_refl) by (apply UIP_refl); subst. reflexivity.
Defined.

Definition typ'D {n} (t : typ' n) : type_for_arity n.
Proof.
  unfold typ', typ_map, list_to_pmap, type_nth in t; simpl in t.
  destruct t as [p v].
  unfold type_nth in v.
  pmap_lookup'_simpl.
  apply list_typD; assumption.
  apply base_typD; assumption.
Defined.

Global Instance TypeView_list_typ' : PartialView (typ' 1) (list_typ 1) :=
  PartialViewPMap_Type 2 (typ_map) eq_refl 1.
  
Global Instance TypeView_base_typ' : PartialView (typ' 0) (base_typ 0) :=
  PartialViewPMap_Type 1 typ_map eq_refl 0.
  
Instance TypeView_list_typ : PartialView typ (list_typ 1 * typ).
eapply PartialView_trans. 
apply TypeView_sym1.
eapply (@PartialView_prod _ _ _ _ _ PartialView_id). 
Defined.

Instance TypeView_base_typ : PartialView typ (base_typ 0).
eapply PartialView_trans. 
eapply TypeView_sym0.
apply TypeView_base_typ'.
Defined.

Definition TSymAll_typ_map : TSym_All typ_map.
  repeat first [eapply TSym_All_Branch_None |
                eapply TSym_All_Branch_Some; [eapply _ | |] |
                eapply TSym_All_Empty].
Defined.

Global Instance TSym_typ' : TSym typ'.
  apply TSymOneOf. apply TSymAll_typ_map.
Defined.


Global Instance RType_typ : RType typ.
apply RType_mtyp. 
apply _.
Defined.

Global Instance RTypeOk_typ : RTypeOk.
apply RTypeOk_mtyp.
Defined.

Global Instance Typ2_tyArr : Typ2 RType_typ Fun := Typ2_Fun.
Global Instance Typ2Ok_tyArr : Typ2Ok Typ2_tyArr := Typ2Ok_Fun.

Global Instance Typ0_tyProp : Typ0 RType_typ Prop := Typ0_sym tyProp.
Global Instance Typ0Ok_tyProp : Typ0Ok Typ0_tyProp := Typ0Ok_sym tyProp.

Global Instance Typ0_tyNat : Typ0 RType_typ nat := Typ0_sym tyNat.
Global Instance Typ0Ok_tyNat : Typ0Ok Typ0_tyNat := Typ0Ok_sym tyNat.

Global Instance Typ0_tyString : Typ0 RType_typ String.string := Typ0_sym tyString.
Global Instance Typ0Ok_tyString : Typ0Ok Typ0_tyString := Typ0Ok_sym tyString.

Global Instance Typ0_tyBool : Typ0 RType_typ bool := Typ0_sym tyBool.
Global Instance Typ0Ok_tyBool : Typ0Ok Typ0_tyBool := Typ0Ok_sym tyBool.

Global Instance Typ1_tyList : Typ1 RType_typ list := Typ1_sym (f_insert tList).
Global Instance Typ1Ok_tyList : Typ1Ok Typ1_tyList := Typ1Ok_sym (f_insert tList).

Section ReifyType.

Global Instance Reify_typ : Reify typ := 
  Reify_typ typ (reify_base_typ typ ::
                 reify_list_typ typ :: nil).

End ReifyType.

