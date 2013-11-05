Require Import ExtLib.Recur.Relation.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.Injection.
Require Import ExtLib.Tactics.EqDep.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.ExprCore.
Require Import MirrorCore.Ext.ExprD.

Set Implicit Arguments.
Set Strict Implicit.

Global Instance Injective_tvArr a b c d : Injective (tvArr a b = tvArr c d) :=
{ result := a = c /\ b = d }.
Proof. abstract (inversion 1; intuition). Defined.

Global Instance Injective_tvType a b : Injective (tvType a = tvType b) :=
{ result := a = b }.
Proof. abstract (inversion 1; intuition). Defined.

Global Instance Injective_typ_cast_typ_hetero_Some ts f a b c p
: Injective (typ_cast_typ ts f a b c = Some p) :=
{ result := exists pf : b = c,
              match pf in _ = t
                    return f (typD ts a b) -> f (typD ts a t)
              with
                | eq_refl => fun x => x
              end = p }.
Proof.
  abstract (intros; exists (typ_cast_typ_eq _ _ _ _ _ H);
                           uip_all;
                           subst; rewrite typ_cast_typ_refl in H; f_equal; inv_all; auto).
Defined.

(** TODO: solve expr_acc trans as a type class *)

Ltac wf_expr_ind :=
  refine (@Fix _ _ (wf_rightTrans wf_expr_acc) _ _).

Ltac red_exprD :=
  repeat match goal with
           | H : context [ @ExprD.exprD _ _ _ _ _ _ _ ] |- _ =>
             repeat progress (autorewrite with exprD_rw in H ; simpl in H)
           | |- context [ @ExprD.exprD _ _ _ _ _ _ _ ] =>
             repeat progress (autorewrite with exprD_rw; simpl)
         end.
