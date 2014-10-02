Require Import Coq.Bool.Bool.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.HList.
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
  Unset Elimination Schemes.
  Inductive expr : Type :=
  | Var : var -> expr
  | Inj : func -> expr
  | App : expr -> expr -> expr
  | Abs : typ -> expr -> expr
  | UVar : uvar -> list expr -> expr.

  Theorem expr_ind
  : forall P : expr -> Prop,
      (forall v : var, P (Var v)) ->
      (forall f0 : func, P (Inj f0)) ->
      (forall e : expr, P e -> forall e0 : expr, P e0 -> P (App e e0)) ->
      (forall (t : typ) (e : expr), P e -> P (Abs t e)) ->
      (forall (u : uvar) (l : list expr), Forall P l -> P (UVar u l)) ->
      forall e : expr, P e.
  Proof.
    intros P Hvar Hinj Happ Habs Huvar.
    refine (fix expr_ind e : P e :=
              match e with
                | Var v => Hvar v
                | Inj i => Hinj i
                | App l r => Happ _ (expr_ind l) _ (expr_ind r)
                | Abs t e => Habs _ _ (expr_ind e)
                | UVar u es =>
                  Huvar u es ((fix build ls : Forall P ls :=
                                 match ls with
                                   | nil => Forall_nil P
                                   | l :: ls => Forall_cons _ (expr_ind l) (build ls)
                                 end) es)
              end).
  Qed.

  Theorem expr_rect
  : forall P : expr -> Type,
      (forall v : var, P (Var v)) ->
      (forall f0 : func, P (Inj f0)) ->
      (forall e : expr, P e -> forall e0 : expr, P e0 -> P (App e e0)) ->
      (forall (t : typ) (e : expr), P e -> P (Abs t e)) ->
      (forall (u : uvar) (l : list expr), hlist P l -> P (UVar u l)) ->
      forall e : expr, P e.
  Proof.
    intros P Hvar Hinj Happ Habs Huvar.
    refine (fix expr_rect e : P e :=
              match e with
                | Var v => Hvar v
                | Inj i => Hinj i
                | App l r => Happ _ (expr_rect l) _ (expr_rect r)
                | Abs t e => Habs _ _ (expr_rect e)
                | UVar u es =>
                  Huvar u es ((fix build ls : hlist P ls :=
                                 match ls with
                                   | nil => Hnil
                                   | l :: ls => Hcons (expr_rect l) (build ls)
                                 end) es)
              end).
  Defined.
  Set Elimination Schemes.

  Inductive IIn {T} (x : T) : list T -> Prop :=
  | IInH : forall ls, IIn x (x :: ls)
  | IInN : forall y ls, IIn x ls -> IIn x (y :: ls).

  Inductive expr_acc (e : expr) : expr -> Prop :=
  | acc_App_l : forall a, expr_acc e (App e a)
  | acc_App_r : forall f, expr_acc e (App f e)
  | acc_Abs : forall t, expr_acc e (Abs t e)
  | acc_UVar : forall u es, IIn e es -> expr_acc e (UVar u es).

  Definition exprs : Type := list expr.

  Definition wf_expr_acc : well_founded expr_acc :=
    fix recurse a : Acc expr_acc a :=
      match a as a return Acc expr_acc a with
        | Var v =>
           Acc_intro _ (fun y (pf : expr_acc _ (Var v)) =>
                          match pf in expr_acc _ z
                                return match z return Prop with
                                         | Var _ => Acc expr_acc y
                                         | _ => True
                                       end
                          with
                            | acc_App_l _ => I
                            | _ => I
                          end)
         | Inj i =>
           Acc_intro _ (fun y (pf : expr_acc _ (Inj i)) =>
                          match pf in expr_acc _ z
                                return match z return Prop with
                                         | Inj _ => Acc expr_acc y
                                         | _ => True
                                       end
                          with
                            | acc_App_l _ => I
                            | _ => I
                          end)
         | App f x =>
           Acc_intro _ (fun y (pf : expr_acc y (App f x)) =>
                          match pf in expr_acc _ z
                                return match z return Prop with
                                         | App a b =>
                                           (unit -> Acc expr_acc a) ->
                                           (unit -> Acc expr_acc b) ->
                                           Acc expr_acc y
                                         | _ => True
                                       end
                          with
                            | acc_App_l z => fun a _ => a tt
                            | acc_App_r _ => fun _ a => a tt
                            | _ => I
                          end (fun _ => recurse f) (fun _ => recurse x))
         | Abs t x =>
           Acc_intro _ (fun y (pf : expr_acc y (Abs t x)) =>
                          match pf in expr_acc _ z
                                return match z return Prop with
                                         | Abs t b =>
                                           (unit -> Acc expr_acc b) ->
                                           Acc expr_acc y
                                         | _ => True
                                       end
                          with
                            | acc_Abs _ => fun a => a tt
                            | _ => I
                          end (fun _ => recurse x))
         | UVar u es =>
           Acc_intro _ (fun y (pf : expr_acc y (UVar u es)) =>
                          match pf in expr_acc _ z
                                return match z return Prop with
                                         | UVar u es =>
                                           (forall e, IIn e es ->
                                                      Acc expr_acc e) ->
                                           Acc expr_acc y
                                         | _ => True
                                       end
                          with
                            | acc_UVar _ e pf => fun x => x _ pf
                            | _ => I
                          end (fun i =>
                                 (fix get es (pf : IIn i es) {struct es}
                                  : Acc _ i :=
                                    match pf in IIn _ es
                                          return match es return Prop with
                                                   | nil => True
                                                   | x :: xs =>
                                                     (unit -> Acc _ x) *
                                                     (IIn i xs -> Acc _ i)
                                                 end ->
                                                 Acc _ i
                                    with
                                      | IInH _ => fun k => fst k tt
                                      | IInN _ _ pf => fun k => snd k pf
                                    end match es as es
                                              return match es return Prop with
                                                       | nil => True
                                                       | x :: xs =>
                                                         (unit -> Acc expr_acc x) *
                                                         (IIn i xs -> Acc expr_acc i)
                                                     end
                                        with
                                          | nil => I
                                          | x :: xs => (fun _ => recurse x,
                                                        fun pf => get xs pf)
                                        end) es))
       end.

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
    intros. eapply Huvar. clear - H.
    cut (forall y, IIn y l -> P y).
    { clear. admit. }
    { intro. specialize (H y).
      intro. apply H. constructor. constructor. assumption. }
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
