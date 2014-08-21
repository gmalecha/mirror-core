Require Import Coq.Bool.Bool.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.List.
Require Import ExtLib.Relations.TransitiveClosure.
Require Import ExtLib.Recur.Relation.

Set Implicit Arguments.
Set Strict Implicit.

Section env.
  Variable typ : Type.
  Variable func : Type.
  Definition var := nat.
  Definition uvar := nat.

  (** TODO(gmalecha): Putting [typ] and [func] in a module would
   ** reduce the number of parameters here.
   **)
  Inductive expr : Type :=
  | Var : var -> expr
  | Inj : func -> expr
  | App : expr -> expr -> expr
  | Abs : typ -> expr -> expr
  | UVar : uvar -> list expr -> expr.

  Inductive expr_acc : expr -> expr -> Prop :=
  | acc_App_l : forall f a, expr_acc f (App f a)
  | acc_App_r : forall f a, expr_acc a (App f a)
  | acc_Abs : forall t e, expr_acc e (Abs t e)
  | acc_UVar : forall u es e, In e es -> expr_acc e (UVar u es).

  Definition exprs : Type := list expr.

  Theorem wf_expr_acc : well_founded expr_acc.
  Proof.
    clear. red.
(*    refine (fix recurse a : Acc expr_acc a :=
              match a as a return Acc expr_acc a with
                | Var v => Acc_intro _ (fun y pf => match pf in expr_acc _ z return match z return Prop with
                                                                                      | Var v => Acc expr_acc y
                                                                                      | _ => True
                                                                                    end
                                                    with
                                                      | acc_App_l _ _ => _
                                                      | _ => _
                                                    end)
                | App f x => _
                | _ => _
              end) ;
    try solve [ inversion H ].
constructor.
Show Proof.
*)
  Admitted.

  Theorem expr_strong_ind
  : forall (P : expr -> Prop),
      (forall v, P (Var v)) ->
      (forall u es, Forall P es -> P (UVar u es)) ->
      (forall i, P (Inj i)) ->
      (forall a b, (forall e, (leftTrans expr_acc) e (App a b) -> P e) -> P (App a b)) ->
      (forall t a, (forall e, (leftTrans expr_acc) e (Abs t a) -> P e) -> P (Abs t a)) ->
      forall e, P e.
  Proof.
    intros P Hvar Huvar Hinj Happ Habs.
    eapply Fix. eapply wf_leftTrans. eapply wf_expr_acc.
    destruct x; auto.
    intros. eapply Huvar. clear - H. admit.
  Qed.

  Variable RelDec_eq_typ : RelDec (@eq typ).
  Variable RelDec_eq_func : RelDec (@eq func).

  Definition variables := list typ.

  Fixpoint expr_eq_dec (e1 e2 : expr) : bool :=
    match e1 , e2 with
      | Var v1 , Var v2 => EqNat.beq_nat v1 v2
      | UVar v1 es1 , UVar v2 es2 =>
        if EqNat.beq_nat v1 v2 then
          (fix go a b : bool :=
             match a , b with
               | nil , nil => true
               | x :: xs , y :: ys => expr_eq_dec x y && go xs ys
               | _ , _ => false
             end)
            es1 es2
        else false
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

  Variable RelDec_Correct_typ : RelDec_Correct RelDec_eq_typ.
  Variable RelDec_Correct_func : RelDec_Correct RelDec_eq_func.

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
             | |- context [ ?X ?[ @eq ?T ]?Y ] =>
               change (X ?[ @eq T ] Y) with (X ?[ eq ] Y) ;
                 rewrite rel_dec_correct
             | |- context [ List.list_eqb RelDec_eq_typ ?X ?Y ] =>
               change (List.list_eqb RelDec_eq_typ X Y) with (X ?[ eq ] Y) ;
                 rewrite rel_dec_correct
             | |- _ => rewrite andb_true_iff
             | H : forall x, (_ = true) <-> _ |- _ => rewrite H
           end; try solve [ intuition congruence ].
    admit.
  Qed.

  Global Instance RelDec_eq_expr : RelDec (@eq expr) :=
  { rel_dec := expr_eq_dec }.

  Global Instance RelDecCorrect_eq_expr : RelDec_Correct RelDec_eq_expr.
  Proof.
    constructor. eapply expr_eq_dec_eq.
  Qed.

  Section mentionsU.
    Variable u : uvar.

    Fixpoint mentionsU (e : expr) : bool :=
      match e with
        | Var _
        | Inj _ => false
        | UVar u' us =>
          if EqNat.beq_nat u u' then true
          else List.existsb mentionsU us
        | App f e => if mentionsU f then true else mentionsU e
        | Abs _ e => mentionsU e
      end.
  End mentionsU.

  Section mentionsV.
    Fixpoint mentionsV (v : var) (e : expr) : bool :=
      match e with
        | Var v' => v ?[ eq ] v'
        | Inj _ => false
        | UVar _ us => List.existsb (mentionsV v) us
        | App a b => if mentionsV v a then true else mentionsV v b
        | Abs _ e => mentionsV (S v) e
      end.
  End mentionsV.

End env.

Arguments Var {typ func} _.
Arguments Inj {typ func} _.
Arguments UVar {typ func} _ _.
Arguments App {typ func} _ _.
Arguments Abs {typ func} _ _.
Arguments mentionsU {typ func} _ _.
Arguments mentionsV {typ func} _ _.
