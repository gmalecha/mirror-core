(* A type system for Expr
 * This achieves a phase split between the 'well-formedness' of expressions
 * and their meaning
 *)
Require Import List Bool.
Require Import Coq.FSets.FMapPositive.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.EqDep.
Require Import ExtLib.Tactics.Injection.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.ExprCore.

Set Implicit Arguments.
Set Strict Implicit.

Require FMapFacts.

Module PMAP_FACTS := FMapFacts.Facts PositiveMap.
Module PMAP_PROPS := FMapFacts.Properties PositiveMap.

Section typed.
  Variable types : types.

  Definition WellTyped_func (tf : tfunction) (f : function types) : Prop :=
    tf.(tfenv) = f.(fenv) /\ tf.(tftype) = f.(ftype).

  Definition typeof_func (f : function types) : tfunction :=
  {| tfenv := fenv f ; tftype := ftype f |}.

  Definition WellTyped_funcs (tfs : tfunctions) (fs : functions types) : Prop :=
    PositiveMap.map typeof_func fs = tfs.

  Definition  WellTyped_env (tes : tenv typ) (es : env (typD types)) : Prop :=
    Forall2 (fun x y => x = projT1 y) tes es.

  Definition typeof_funcs : functions types -> tfunctions :=
    PositiveMap.map typeof_func.

  Theorem WellTyped_func_typeof_func : forall tf f,
    WellTyped_func tf f <-> tf = typeof_func f.
  Proof.
    compute; destruct f; destruct tf; intuition; subst; auto.
    inversion H; clear H; subst; auto.
    inversion H; clear H; subst; auto.
  Qed.

  Theorem WellTyped_funcs_typeof_funcs : forall tfs fs,
    WellTyped_funcs tfs fs <-> tfs = typeof_funcs fs.
  Proof.
    intuition. red. symmetry; auto.
  Qed.

  Theorem WellTyped_env_typeof_env : forall e te,
    WellTyped_env te e <-> te = typeof_env e.
  Proof.
    induction e; simpl; intros.
    { intuition; subst. inversion H; auto. constructor. }
    { intuition; subst. inversion H; clear H; subst. f_equal; eauto.
      eapply IHe; eauto. constructor; auto. eapply IHe. auto. }
  Qed.

  Lemma typeof_env_app : forall ts (a b : EnvI.env (typD ts)),
    EnvI.typeof_env (a ++ b) = EnvI.typeof_env a ++ EnvI.typeof_env b.
  Proof.
    unfold EnvI.typeof_env; intros.
    rewrite map_app. reflexivity.
  Qed.

  Lemma typeof_env_length : forall ts (a : EnvI.env (typD ts)),
    length (EnvI.typeof_env a) = length a.
  Proof.
    unfold EnvI.typeof_env; intros.
    rewrite map_length. reflexivity.
  Qed.

  Section typeof_expr.
    Variable fs : tfunctions.
    Variable uvars : tenv typ.

    Fixpoint typeof_expr (var_env : tenv typ) (e : expr) : option typ :=
      match e with
        | Var x  => nth_error var_env x
        | UVar x => nth_error uvars x
        | Func f ts =>
          match tfunc_lookup fs f with
            | None => None
            | Some r =>
              if EqNat.beq_nat (length ts) (tfenv r) then
                Some (instantiate_typ ts (tftype r))
              else
                None
          end
        | App e e' =>
          Monad.bind (typeof_expr var_env e) (fun tf =>
          Monad.bind (typeof_expr var_env e') (fun tx =>
          type_of_apply tf tx))
        | Abs t e =>
          match typeof_expr (t :: var_env) e with
            | None => None
            | Some t' => Some (tvArr t t')
          end
        | Equal t e1 e2 =>
          match typeof_expr var_env e1 with
            | Some t' =>
              if t ?[ eq ] t' then
                match typeof_expr var_env e2 with
                  | Some t' =>
                    if t ?[ eq ] t' then Some tvProp else None
                  | None => None
                end
              else None
            | None => None
          end
        | Not e =>
          match typeof_expr var_env e with
            | Some t' => if tvProp ?[ eq ] t' then Some tvProp else None
            | None => None
          end
      end.

    Definition WellTyped_expr (var_env : tenv typ) (e : expr) (t : typ) : Prop :=
      typeof_expr var_env e = Some t.

    Definition typecheck_expr (var_env : tenv typ) (e : expr) (t : typ) : bool :=
      typeof_expr var_env e ?[ eq ] Some t.

    Theorem WellTyped_expr_Var : forall g v t',
      WellTyped_expr g (Var v) t' <-> nth_error g v = Some t'.
    Proof.
      unfold WellTyped_expr; simpl; intros; intuition.
    Qed.

    Theorem WellTyped_expr_Func : forall g f t' aps,
      WellTyped_expr g (Func f aps) t' <->
      (exists ft,
         tfunc_lookup fs f = Some ft /\
         length aps = tfenv ft /\
         instantiate_typ aps (tftype ft) = t').
    Proof.
      Opaque lookup.
      unfold WellTyped_expr; simpl; intros.
      destruct (tfunc_lookup fs f).
      { consider (EqNat.beq_nat (length aps) (tfenv t));
        try congruence; intuition.
        { inversion H0; clear H0; subst. eexists; eauto. }
        { destruct H0. intuition. inversion H1; subst; auto. }
        congruence.
        destruct H0. intuition. exfalso. inversion H1; clear H1; subst. auto. }
      { intuition; try congruence.
        destruct H. intuition congruence. }
    Qed.

    Theorem WellTyped_expr_UVar : forall g v t',
      WellTyped_expr g (UVar v) t' <-> nth_error uvars v = Some t'.
    Proof.
      unfold WellTyped_expr; simpl; intros; intuition.
    Qed.

    Theorem WellTyped_expr_Not : forall g e t,
      WellTyped_expr g (Not e) t <-> (t = tvProp /\ WellTyped_expr g e tvProp).
    Proof.
      Opaque rel_dec.
      unfold WellTyped_expr; simpl; intros.
      destruct (typeof_expr g e); intuition try congruence.
      { consider (tvProp ?[ eq ] t0); congruence. }
      { consider (tvProp ?[ eq ] t0); try congruence. }
      { subst. inversion H1; clear H1; subst.
        match goal with
          | |- (if ?X then _ else _) = _ =>
            consider X; intros; try reflexivity
        end.
        intuition. }
    Qed.

    Theorem WellTyped_expr_Equal : forall g e1 e2 t t',
      WellTyped_expr g (Equal t e1 e2) t' <->
      (t' = tvProp /\ WellTyped_expr g e1 t /\ WellTyped_expr g e2 t).
    Proof.
      unfold WellTyped_expr; simpl; intros.
      destruct (typeof_expr g e1); destruct (typeof_expr g e2);
      intros; split; intros;
      repeat match goal with
               | [ H : _ /\ _ |- _ ] => destruct H
               | [ H : context [ if ?X then _ else _ ] |- _ ] =>
                 consider X; intros; subst
               | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
             end; auto; try congruence.
      { consider (t ?[ eq ] t); intuition. }
    Qed.

    Theorem WellTyped_expr_Abs : forall g e t t',
      WellTyped_expr g (Abs t e) t' <->
      exists t'', t' = tvArr t t'' /\ WellTyped_expr (t :: g) e t''.
    Proof.
      unfold WellTyped_expr; simpl; intros.
      destruct (typeof_expr (t :: g) e); intuition; inv_all; subst; eauto.
      destruct H; intuition; inv_all; subst; auto.
      congruence.
      destruct H; intuition; congruence.
    Qed.

    Theorem WellTyped_expr_App : forall g e e' t,
      WellTyped_expr g (App e e') t <->
      (exists tf tx,
         WellTyped_expr g e tf /\
         WellTyped_expr g e' tx /\
         type_of_apply tf tx = Some t).
    Proof.
      unfold WellTyped_expr; simpl; intros.
      destruct (typeof_expr g e).
      { destruct (typeof_expr g e').
        { intuition eauto.
          do 2 destruct H; intuition. inv_all; subst; auto. }
        { intuition try congruence. do 2 destruct H; intuition congruence. } }
      { intuition; try congruence. do 2 destruct H. intuition congruence. }
    Qed.

    (** NOTE: This is suboptimal **)
(*
    Theorem WellTyped_expr_det : forall g e t1 t2,
      WellTyped_expr g e t1 ->
      WellTyped_expr g e t2 ->
      t1 = t2.
    Proof.
      unfold WellTyped_expr. intros. rewrite H in H0. congruence.
    Qed.
*)
  End typeof_expr.

  Theorem lookup_typeof_funcs : forall (fs : functions types) (n : func),
    tfunc_lookup (typeof_funcs fs) n =
    match func_lookup fs n with
      | None => None
      | Some x => Some (typeof_func x)
    end.
  Proof.
    unfold tfunc_lookup, func_lookup, typeof_funcs; intros.
    rewrite PMAP_FACTS.map_o.
    reflexivity.
  Qed.

  Theorem nth_error_typeof_env : forall (fs : env (typD types)) n,
    nth_error (typeof_env fs) n = match nth_error fs n with
                                    | None => None
                                    | Some x => Some (projT1 x)
                                  end.
  Proof.
    unfold typeof_env; intros.
    rewrite nth_error_map. reflexivity.
  Qed.

End typed.
