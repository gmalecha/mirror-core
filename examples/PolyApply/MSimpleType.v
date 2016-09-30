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
Require Import MirrorCore.syms.SymOneOf.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.MTypes.ListType.
Require Import MirrorCore.MTypes.BaseType.
Require Import MirrorCore.Views.ViewSumN.

Set Implicit Arguments.
Set Strict Implicit.

Import OneOfType.

Definition typ_map x := 
  list_to_pmap
    (pcons (base_typ x)
           (pcons (list_typ x)
                  pnil)).

Definition typ' x := OneOf (typ_map x).

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
  unfold typ_map, list_to_pmap in *. simpl in *.
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
  unfold typ', typ_map, list_to_pmap in t; simpl in t.
  destruct t as [p v].
  pmap_lookup'_simpl.
  apply list_typD; assumption.
  apply base_typD; assumption.
Defined.

Global Instance TypeView_list_typ' : PartialView (typ' 1) (list_typ 1) :=
  PartialViewPMap 2 (typ_map 1) eq_refl.
  
Global Instance TypeView_base_typ' : PartialView (typ' 0) (base_typ 0) :=
  PartialViewPMap 1 (typ_map 0) eq_refl.
  
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


