Require Import Coq.Classes.Morphisms.
Require Import Coq.Bool.Bool.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Prop.
Require Import ExtLib.Data.List.
Require Import ExtLib.Relations.TransitiveClosure.
Require Import ExtLib.Recur.Relation.
Require Import ExtLib.Tactics.

Set Implicit Arguments.
Set Strict Implicit.

Section env.
  Variable typ : Type.
  Variable func : Type.
  Definition var := nat.
  Definition uvar := nat.

  (** NOTE: Putting [typ] and [func] in a module would
   ** reduce the number of parameters here.
   **)
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
  Defined.

  Theorem expr_strong_ind
  : forall (P : expr -> Prop),
      (forall v, P (Var v)) ->
      (forall u, P (UVar u)) ->
      (forall i, P (Inj i)) ->
      (forall a b, (forall e, (leftTrans expr_acc) e (App a b) -> P e) -> P (App a b)) ->
      (forall t a, (forall e, (leftTrans expr_acc) e (Abs t a) -> P e) -> P (Abs t a)) ->
      forall e, P e.
  Proof.
    intros P Hvar Huvar Hinj Happ Habs.
    eapply Fix. eapply wf_leftTrans. eapply wf_expr_acc.
    destruct x; auto.
  Qed.

  Theorem expr_strong_ind_no_case
  : forall (P : expr -> Prop),
      (forall e, (forall e', (leftTrans expr_acc) e' e -> P e') -> P e) ->
      forall e, P e.
  Proof.
    intros P H.
    eapply Fix.
    exact (wf_leftTrans wf_expr_acc).
    eauto.
  Qed.

  Section sdec.
    Variable RelDec_eq_typ : RelDec (@eq typ).
    Variable func_eq : func -> func -> bool.

    Fixpoint expr_eq_sdec (e1 e2 : expr) : bool :=
      match e1 , e2 with
      | Var v1 , Var v2 => EqNat.beq_nat v1 v2
      | UVar v1 , UVar v2 => EqNat.beq_nat v1 v2
      | Inj f1 , Inj f2 => func_eq f1 f2
      | App f1 e1 , App f2 e2 =>
        if expr_eq_sdec f1 f2 then
          expr_eq_sdec e1 e2
        else
          false
      | Abs t1 e1 , Abs t2 e2 =>
        if t1 ?[ eq ] t2 then expr_eq_sdec e1 e2
        else false
      | _ , _ => false
      end.

    Variable RelDec_Correct_typ : RelDec_Correct RelDec_eq_typ.
    Variable func_eq_ok : forall a b, func_eq a b = true -> a = b.

    Theorem expr_eq_sdec_ok : forall e1 e2,
        expr_eq_sdec e1 e2 = true ->
        e1 = e2.
    Proof.
      induction e1; destruct e2; simpl; intros; try congruence.
      { eapply EqNat.beq_nat_true in H. congruence. }
      { eapply func_eq_ok in H. congruence. }
      { apply Bool.andb_true_iff in H.
        destruct H. eapply IHe1_1 in H. eapply IHe1_2 in H0. congruence. }
      { consider (t ?[ eq ] t0).
        intros. apply IHe1 in H0. congruence. }
      { eapply EqNat.beq_nat_true in H. congruence. }
    Qed.
  End sdec.

  Variable RelDec_eq_typ : RelDec (@eq typ).
  Variable RelDec_eq_func : RelDec (@eq func).

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
  Qed.

  Global Instance RelDec_eq_expr : RelDec (@eq expr) :=
  { rel_dec := expr_eq_dec }.

  Global Instance RelDecCorrect_eq_expr : RelDec_Correct RelDec_eq_expr.
  Proof.
    constructor. eapply expr_eq_dec_eq.
  Qed.

  Section mentionsAny.
    Variable (uP : uvar -> bool).

    Fixpoint mentionsAny (vP : var -> bool) (e : expr) : bool :=
      match e with
        | Var v => vP v
        | Inj _ => false
        | UVar u => uP u
        | App f e => if mentionsAny vP f then true else mentionsAny vP e
        | Abs _ e => mentionsAny (fun v => match v with
                                             | 0 => false
                                             | S v => vP v
                                           end) e
      end.
  End mentionsAny.

  Lemma Proper_mentionsAny
  : Proper ((@eq uvar ==> @eq bool) ==>
            (@eq var ==> @eq bool) ==>
            @eq _ ==> @eq bool) mentionsAny.
  Proof.
    repeat red. intros; subst.
    revert x0 y0 x y H0 H.
    induction y1; simpl; intros; auto.
    { erewrite IHy1_1; eauto. erewrite IHy1_2; eauto. }
    { eapply IHy1; eauto.
      red. intros; subst. destruct y2; eauto. }
  Qed.

  Lemma mentionsAny_factor
  : forall (fu fu' : uvar -> bool) (e : expr) (fv fv' : var -> bool),
      mentionsAny (fun u : uvar => fu u || fu' u)
                  (fun v : var => fv v || fv' v) e =
      mentionsAny fu fv e || mentionsAny fu' fv' e.
  Proof.
    induction e; simpl; auto; intros; Cases.rewrite_all_goal.
    { forward. simpl. rewrite orb_true_r. reflexivity. }
    { rewrite <- IHe. eapply Proper_mentionsAny; eauto.
      reflexivity. clear. red. intros; subst.
      destruct y; auto. }
  Qed.

  Section mentionsU.
    Variable u : uvar.

    Fixpoint _mentionsU (e : expr) : bool :=
      match e with
        | Var _
        | Inj _ => false
        | UVar u' => EqNat.beq_nat u u'
        | App f e => if _mentionsU f then true else _mentionsU e
        | Abs _ e => _mentionsU e
      end.

    Theorem _mentionsU_mentionsU
    : forall e,
        _mentionsU e = mentionsAny (fun u' => u ?[ eq ] u') (fun _ => false) e.
    Proof.
      induction e; simpl; intros; auto.
      - rewrite <- IHe1. rewrite <- IHe2. reflexivity.
      - rewrite IHe. eapply Proper_mentionsAny; eauto.
        reflexivity. red. intros; subst; destruct y; reflexivity.
    Qed.
  End mentionsU.

  Section mentionsV.
    Fixpoint _mentionsV (v : var) (e : expr) : bool :=
      match e with
        | Var v' => v ?[ eq ] v'
        | Inj _
        | UVar _ => false
        | App a b => if _mentionsV v a then true else _mentionsV v b
        | Abs _ e => _mentionsV (S v) e
      end.

    Theorem _mentionsV_mentionsV
    : forall e v,
        _mentionsV v e = mentionsAny (fun _ => false) (fun v' => v ?[ eq ] v') e.
    Proof.
      induction e; simpl; intros; auto.
      - rewrite <- IHe1. rewrite <- IHe2. reflexivity.
      - rewrite IHe. eapply Proper_mentionsAny; eauto.
        reflexivity. red. intros; subst; destruct y; reflexivity.
    Qed.
  End mentionsV.

  Lemma mentionsAny_complete
  : forall (pu : uvar -> bool) (e : expr) (pv : var -> bool),
      mentionsAny pu pv e = true <->
      (exists u : uvar, _mentionsU u e = true /\ pu u = true) \/
      (exists v : var, _mentionsV v e = true /\ pv v = true).
  Proof.
    induction e; simpl; intros.
    { split.
      - right.
        eexists; split; try eassumption.
        eapply rel_dec_correct. reflexivity.
      - destruct 1.
        + forward_reason; congruence.
        + forward_reason.
          eapply (@rel_dec_correct _ (@eq var)) in H;
            eauto with typeclass_instances. }
    { split; try congruence. destruct 1; forward_reason; congruence. }
    { specialize (IHe1 pv); specialize (IHe2 pv).
      destruct (mentionsAny pu pv e1).
      - split; eauto. intro. apply IHe1 in H.
        destruct H; forward_reason.
        + left; eexists. split; try eassumption. rewrite H. reflexivity.
        + right; eexists; split; try eassumption. rewrite H. reflexivity.
      - rewrite IHe2; clear IHe2.
        split.
        + destruct 1; forward_reason;
          try first [ left ; eexists; split; [ | eassumption ]
                    | right ; eexists; split; [ | eassumption ] ].
          * rewrite H. destruct (_mentionsU x e1); reflexivity.
          * rewrite H. destruct (_mentionsV x e1); reflexivity.
        + destruct 1; forward_reason.
          { consider (_mentionsU x e1); intros.
            - left; eexists; split; try eauto.
              consider (_mentionsU x e2); auto.
              intro. apply IHe1. left; eauto.
            - left; eexists; split; try eauto. }
          { consider (_mentionsV x e1); intros.
            - cut (false = true); try congruence.
              apply IHe1. right; eauto.
            - right. eauto. } }
    { rewrite IHe.
      eapply or_iff_compat_l.
      clear. split; intros; forward_reason.
      - forward. subst. eauto.
      - exists (S x). eauto. }
    { split; intros.
      - left; eexists; split; try eassumption.
        consider (EqNat.beq_nat u u); auto.
      - destruct H; forward_reason; try congruence.
        consider (EqNat.beq_nat x u); auto.
        destruct 1. assumption. }
  Qed.

  Lemma mentionsAny_weaken
  : forall pu pu' pv pv' e,
      (forall u, _mentionsU u e = true -> pu u = false -> pu' u = false) ->
      (forall v, _mentionsV v e = true -> pv v = false -> pv' v = false) ->
      mentionsAny pu pv e = false ->
      mentionsAny pu' pv' e = false.
  Proof.
    intros pu pu' pv pv' e Hu Hv; revert pv pv' Hv.
    induction e; simpl; intros; auto.
    { eapply Hv. eapply rel_dec_eq_true; eauto with typeclass_instances.
      eauto. }
    { forward. simpl in *.
      erewrite IHe1; try eassumption.
      eapply IHe2; try eassumption.
      - intros. eapply Hu.
        rewrite H1. destruct (_mentionsU u e1); auto. auto.
      - intros. eapply Hv. rewrite H1. destruct (_mentionsV v e1); auto. auto.
      - intros. eapply Hu; eauto. rewrite H1; auto.
      - intros. eapply Hv. rewrite H1; eauto. eauto. }
    { eapply IHe. eauto. 2: eassumption. simpl.
      destruct v; eauto. }
    { eapply Hu; auto. simpl.
      symmetry. eapply EqNat.beq_nat_refl. }
  Qed.

End env.

Arguments Var {typ func} _.
Arguments Inj {typ func} _.
Arguments UVar {typ func} _.
Arguments App {typ func} _ _.
Arguments Abs {typ func} _ _.
Arguments mentionsAny {typ func} uP vP _.
Arguments _mentionsU {typ func} _ _.
Arguments _mentionsV {typ func} _ _.

Hint Constructors TransitiveClosure.leftTrans : acc_db.
Hint Constructors TransitiveClosure.rightTrans : acc_db.
Hint Constructors expr_acc : acc_db.

