Require Import Bool.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.List.
Require Import ExtLib.Tactics.Injection.
Require Import ExtLib.Tactics.Consider.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Ext.Types.

Set Implicit Arguments.
Set Strict Implicit.

Section env.
  Variable func : Type.
  Definition var := nat.
  Definition uvar := nat.

  Inductive expr : Type :=
  | Var : var -> expr
  | Inj : func -> expr
  | App : expr -> expr -> expr
  | Abs : typ -> expr -> expr
  | UVar : uvar -> expr.

  Inductive expr_acc : expr -> expr -> Prop :=
  | acc_App_l : forall f a, expr_acc f (App f a)
  | acc_App_r : forall f a, expr_acc a (App f a)
  | acc_Abs : forall t e, expr_acc e (Abs t e).

  Definition exprs : Type := list expr.

  Theorem wf_expr_acc : well_founded expr_acc.
  Proof.
    clear. red.
    induction a; simpl; intros; constructor; intros;
    try solve [ inversion H ].
    { inversion H; clear H; subst; auto. }
    { inversion H; clear H; subst; auto. }
  Qed.

  Variable RelDec_func : RelDec (@eq func).

  Definition variables := list typ.

  Fixpoint expr_eq_dec (e1 e2 : expr) : bool :=
    match e1 , e2 with
      | Var v1 , Var v2 => EqNat.beq_nat v1 v2
      | UVar v1 , UVar v2 => EqNat.beq_nat v1 v2
      | Inj f1 , Inj f2 =>
        f1 ?[ eq ] f2
      | App f1 e1 , App f2 e2 =>
        if expr_eq_dec f1 f2 then
          expr_eq_dec e1 e2
        else
          false
      | Abs t1 e1 , Abs t2 e2 =>
        if t1 ?[ eq ] t2 then expr_eq_dec e1 e2
        else false
      | _ , _ => false
    end.

  Variable RelDec_Correct_func : RelDec_Correct RelDec_func.

  Theorem expr_eq_dec_eq : forall e1 e2,
    expr_eq_dec e1 e2 = true <-> e1 = e2.
  Proof.
    induction e1; destruct e2; simpl; intros;
    repeat match goal with
             | |- context [ if ?X then ?Y else false ] =>
               change (if X then Y else false) with (andb X Y)
             | |- context [ EqNat.beq_nat ?X ?Y ] =>
               change (EqNat.beq_nat X Y) with (X ?[ eq ] Y) ;
                 rewrite rel_dec_correct
             | |- context [ ?X ?[ ?Z ] ?Y ] =>
               rewrite rel_dec_correct
             | |- context [ typ_eqb ?X ?Y ] =>
               change (typ_eqb X Y) with (X ?[ eq ] Y) ;
                 rewrite rel_dec_correct
(*             | |- context [ List.list_eq RelDec_eq_typ ?X ?Y ] =>
               change (List.list_eq RelDec_eq_typ X Y) with (X ?[ eq ] Y) ; *)
             | |- context [ ?X ?[ @eq ?T ]?Y ] =>
               change (X ?[ @eq T ] Y) with (X ?[ eq ] Y) ;
                 rewrite rel_dec_correct
             | |- context [ List.list_eqb RelDec_eq_typ ?X ?Y ] =>
               change (List.list_eqb RelDec_eq_typ X Y) with (X ?[ eq ] Y) ;
                 rewrite rel_dec_correct
             | |- _ => rewrite andb_true_iff
             | H : forall x, (_ = true) <-> _ |- _ => rewrite H
           end; try solve [ intuition congruence ].
  Qed.

  Global Instance RelDec_eq_expr : RelDec (@eq expr) :=
  { rel_dec := expr_eq_dec }.

  Global Instance RelDecCorrect_eq_expr : RelDec_Correct RelDec_eq_expr.
  Proof.
    constructor. eapply expr_eq_dec_eq.
  Qed.

(* TODO: this should go elsewhere...
  Definition from_func_list : list function -> functions :=
    from_list.

  Definition func_lookup (fs : functions) (f : func) : option function :=
    PositiveMap.find f fs.

  Definition from_tlist : list tfunction -> tfunctions :=
    from_list.

  Definition tfunc_lookup (fs : tfunctions) (f : func) : option tfunction :=
    PositiveMap.find f fs.
*)

End env.

Arguments Var {func} _.
Arguments Inj {func} _.
Arguments UVar {func} _.
Arguments App {func} _ _.
Arguments Abs {func} _ _.
