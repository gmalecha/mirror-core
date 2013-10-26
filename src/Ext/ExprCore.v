Require Import List Bool.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.Injection.
Require Import ExtLib.Tactics.EqDep.
Require Import ExtLib.Tactics.Consider.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.Ext.Types.

Set Implicit Arguments.
Set Strict Implicit.

Section env.

  Variable types : types.

  Definition func := nat.
  Record tfunction : Type :=
  { tfenv : nat ; tftype : typ }.
  Definition tfunctions := list tfunction.
  Definition var := nat.
  Definition uvar := nat.

  Inductive expr : Type :=
  | Var : var -> expr
  | Func : func -> list typ -> expr
  | App : expr -> expr -> expr
  | Abs : typ -> expr -> expr
  | UVar : uvar -> expr
  | Equal : typ -> expr -> expr -> expr
  | Not : expr -> expr.

  Inductive expr_acc : expr -> expr -> Prop :=
  | acc_App_l : forall f a, expr_acc f (App f a)
  | acc_App_r : forall f a, expr_acc a (App f a)
  | acc_Abs : forall t e, expr_acc e (Abs t e)
  | acc_Equal_l : forall t l r, expr_acc l (Equal t l r)
  | acc_Equal_r : forall t l r, expr_acc r (Equal t l r)
  | acc_Not : forall e, expr_acc e (Not e).

  Definition exprs : Type := list expr.

  Theorem wf_expr_acc : well_founded expr_acc.
  Proof.
    clear. red.
    induction a; simpl; intros; constructor; intros;
    try solve [ inversion H ].
    { inversion H; clear H; subst; auto. }
    { inversion H; clear H; subst; auto. }
    { inversion H; clear H; subst; auto. }
    { inversion H; clear H; subst; auto. }
  Qed.

  Record function := F {
    fenv : nat ;
    ftype : typ ;
    fdenote : parametric fenv nil (fun env => typD types env ftype)
  }.

  Definition functions := list function.
  Definition variables := list typ.

  Variable funcs : functions.
  Variable meta_env : env (typD types).

  Fixpoint expr_eq_dec (e1 e2 : expr) : bool :=
    match e1 , e2 with
      | Var v1 , Var v2 => EqNat.beq_nat v1 v2
      | UVar v1 , UVar v2 => EqNat.beq_nat v1 v2
      | Func f1 ts1 , Func f2 ts2 =>
        if EqNat.beq_nat f1 f2 then
          ts1 ?[ eq ] ts2
        else false
      | App f1 e1 , App f2 e2 =>
        if expr_eq_dec f1 f2 then
          expr_eq_dec e1 e2
        else
          false
      | Abs t1 e1 , Abs t2 e2 =>
        if t1 ?[ eq ] t2 then expr_eq_dec e1 e2
        else false
      | Equal t1 e1 e2 , Equal t1' e1' e2' =>
        if t1 ?[ eq ] t1' then
          if expr_eq_dec e1 e1' then
            if expr_eq_dec e2 e2' then true
            else false
          else false
        else false
      | Not e1 , Not e2 => expr_eq_dec e1 e2
      | _ , _ => false
    end.

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
             | |- context [ typ_eqb ?X ?Y ] =>
               change (typ_eqb X Y) with (X ?[ eq ] Y) ;
                 rewrite rel_dec_correct
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

End env.
