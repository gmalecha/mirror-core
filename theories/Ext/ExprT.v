(* A type system for Expr
 * This achieves a phase split between the 'well-formedness' of expressions
 * and their meaning
 *)
Require Import List.
Require Import Coq.FSets.FMapPositive.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.Injection.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
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
  Variable func : Type.
  Let RType_typ := RType_typ types.
  Local Existing Instance RType_typ.

  Definition  WellTyped_env (tes : tenv typ) (es : env nil) : Prop :=
    Forall2 (fun x y => x = projT1 y) tes es.

  Theorem WellTyped_env_typeof_env : forall e te,
    WellTyped_env te e <-> te = typeof_env e.
  Proof.
    induction e; simpl; intros.
    { intuition; subst. inversion H; auto. constructor. }
    { intuition; subst. inversion H; clear H; subst. f_equal; eauto.
      eapply IHe; eauto. constructor; auto. eapply IHe. auto. }
  Qed.

  Context {RSym_func : RSym func}.

  Lemma typeof_env_app : forall ts (a b : env ts),
    EnvI.typeof_env (a ++ b) = EnvI.typeof_env a ++ EnvI.typeof_env b.
  Proof.
    unfold EnvI.typeof_env; intros.
    rewrite map_app. reflexivity.
  Qed.

  Lemma typeof_env_length : forall ts (a : EnvI.env ts),
    length (EnvI.typeof_env a) = length a.
  Proof.
    unfold EnvI.typeof_env; intros.
    rewrite map_length. reflexivity.
  Qed.

  Section typeof_expr.
    Variable uvars : tenv typ.

    Fixpoint typeof_expr (var_env : tenv typ) (e : expr func) : option typ :=
      match e with
        | Var x  => nth_error var_env x
        | UVar x => nth_error uvars x
        | Inj f => typeof_sym f
        | App e e' =>
          match typeof_expr var_env e
              , typeof_expr var_env e'
          with
            | Some tf , Some tx =>
              type_of_apply tf tx
            | _ , _ => None
          end
        | Abs t e =>
          match typeof_expr (t :: var_env) e with
            | None => None
            | Some t' => Some (tyArr t t')
          end
      end.

    Definition WellTyped_expr (var_env : tenv typ) (e : expr func) (t : typ) : Prop :=
      typeof_expr var_env e = Some t.

    Definition typecheck_expr (var_env : tenv typ) (e : expr func) (t : typ) : bool :=
      typeof_expr var_env e ?[ eq ] Some t.

    Theorem WellTyped_expr_Var : forall g v t',
      WellTyped_expr g (Var v) t' <-> nth_error g v = Some t'.
    Proof. reflexivity. Qed.

    Theorem WellTyped_expr_Sym : forall g f t',
      WellTyped_expr g (Inj f) t' <->
      typeof_sym f = Some t'.
    Proof. reflexivity. Qed.

    Theorem WellTyped_expr_UVar : forall g v t',
      WellTyped_expr g (UVar v) t' <-> nth_error uvars v = Some t'.
    Proof. reflexivity. Qed.

    Theorem WellTyped_expr_Abs : forall g e t t',
      WellTyped_expr g (Abs t e) t' <->
      exists t'', t' = tyArr t t'' /\ WellTyped_expr (t :: g) e t''.
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

  Theorem nth_error_typeof_env : forall (fs : env nil) n,
    nth_error (typeof_env fs) n = match nth_error fs n with
                                    | None => None
                                    | Some x => Some (projT1 x)
                                  end.
  Proof.
    unfold typeof_env; intros.
    rewrite nth_error_map. reflexivity.
  Qed.

End typed.
