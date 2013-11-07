Require Import ExtLib.Recur.Relation.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.Injection.
Require Import ExtLib.Tactics.EqDep.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.ExprCore.
Require Import MirrorCore.Ext.ExprD.

Set Implicit Arguments.
Set Strict Implicit.

Global Instance Injective_tyArr a b c d : Injective (tyArr a b = tyArr c d) :=
{ result := a = c /\ b = d }.
Proof. abstract (inversion 1; intuition). Defined.

Global Instance Injective_tyType a b : Injective (tyType a = tyType b) :=
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
Ltac solve_expr_acc_trans :=
  match goal with
    | |- TransitiveClosure.rightTrans _ _ _ =>
      solve [ eapply TransitiveClosure.RTFin; econstructor
            | eapply TransitiveClosure.RTStep ; [ | eapply acc_App_l ] ; solve_expr_acc_trans
            | eapply TransitiveClosure.RTStep ; [ | eapply acc_App_r ] ; solve_expr_acc_trans
            | eapply TransitiveClosure.RTStep ; [ | eapply acc_Abs ] ; solve_expr_acc_trans ]
  end.

Class SolveTypeClass (T : Type) := result : T.

Hint Extern 0 (SolveTypeClass (TransitiveClosure.rightTrans _ _ _)) =>
  red; solve_expr_acc_trans : typeclass_instances.

Lemma expr_strong_ind (f : Type) (P : expr f -> Prop) : forall
  (IHe : forall e : expr f, (forall y {_ : SolveTypeClass (TransitiveClosure.rightTrans (@expr_acc f) y e)}, P y) -> P e),
  forall e, P e.
Proof.
  intros. revert e.
  refine (@Fix _ _ (wf_rightTrans (@wf_expr_acc f)) _ _).
  intros. eapply IHe. intros; eapply H. eapply result.
Qed.

Ltac wf_expr_ind :=
  eapply expr_strong_ind.

Ltac red_exprD :=
  repeat match goal with
           | H : context [ @ExprD.exprD _ _ _ _ _ _ _ ] |- _ =>
             progress (repeat (autorewrite with exprD_rw in H ; simpl in H))
           | |- context [ @ExprD.exprD _ _ _ _ _ _ _ ] =>
             progress (repeat (autorewrite with exprD_rw; simpl))
            | H : @exprD ?ts ?f ?r ?us ?vs (Abs ?t' ?e) ?t = Some ?v |- _ =>
              eapply (@exprD_Abs ts f r us vs e t t' v) in H ;
              destruct H as [ ? [ ? [ ? ? ] ] ];
              try subst
           | H : @ExprD.exprD _ _ _ _ _ _ _ = Some ?V |- _ =>
             eapply exprD_Abs in H; destruct H as [ ? [ ? [ ? ? ] ] ]
           | |- context [ SymI.symAs _ _ ] =>
             unfold SymI.symAs
           | H : context [ SymI.symAs _ _ ] |- _ =>
             unfold SymI.symAs in H
         end.
