(** A type system for Expr
 ** - This achieves a phase split between the 'well-formedness' of expressions
 **   and their meaning.
 ** - The distinguishing feature for this system is that it holds [typ] as
 **   abstract as possible. It only makes two restrictions:
 **   1) [typ] must include arrow types (with the natural isomorphism)
 **   2) [typ] must include a function [type_of_apply] that determines
 **      the result of applying a type to another type (this operation can fail)
 **)
Require Import List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.Injection.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.Lambda.ExprCore.

Set Implicit Arguments.
Set Strict Implicit.

Section typed.
  Variable typ : Type.
  Variable typD : list Type -> typ -> Type.
  Context {typ_arr : TypInstance2 typD Fun}.
  Let tyArr := @typ2 _ typD _ typ_arr.
  Variable func : Type.

  Definition  WellTyped_env (tes : tenv typ) (es : env typD) : Prop :=
    Forall2 (fun x y => x = projT1 y) tes es.

  Theorem WellTyped_env_typeof_env : forall e te,
    WellTyped_env te e <-> te = typeof_env e.
  Proof.
    induction e; simpl; intros.
    { intuition; subst. inversion H; auto. constructor. }
    { intuition; subst. inversion H; clear H; subst. f_equal; eauto.
      eapply IHe; eauto. constructor; auto. eapply IHe. auto. }
  Qed.

  Context {RFunc_func : RFunc typD func}.

  Lemma typeof_env_app : forall (a b : EnvI.env typD),
    EnvI.typeof_env (a ++ b) = EnvI.typeof_env a ++ EnvI.typeof_env b.
  Proof.
    unfold EnvI.typeof_env; intros.
    rewrite map_app. reflexivity.
  Qed.

  Lemma typeof_env_length : forall (a : EnvI.env typD),
    length (EnvI.typeof_env a) = length a.
  Proof.
    unfold EnvI.typeof_env; intros.
    rewrite map_length. reflexivity.
  Qed.

  Variable type_of_apply : typ -> typ -> option typ.

  Section typeof_expr.
    Variable uvars : tenv typ.

    Fixpoint typeof_expr (var_env : tenv typ) (e : expr typ func) : option typ :=
      match e with
        | Var x  => nth_error var_env x
        | UVar x => nth_error uvars x
        | Inj f => typeof_func f
        | App e e' =>
          Monad.bind (typeof_expr var_env e) (fun tf =>
          Monad.bind (typeof_expr var_env e') (fun tx =>
          type_of_apply tf tx))
        | Abs t e =>
          match typeof_expr (t :: var_env) e with
            | None => None
            | Some t' => Some (tyArr t t')
          end
      end.

    Definition WellTyped_expr (var_env : tenv typ) (e : expr typ func) (t : typ) : Prop :=
      typeof_expr var_env e = Some t.

(*
    Definition typecheck_expr (var_env : tenv typ) (e : expr typ func) (t : typ) : bool :=
      typeof_expr var_env e ?[ eq ] Some t.
*)

    Theorem WellTyped_expr_Var : forall g v t',
      WellTyped_expr g (Var v) t' <-> nth_error g v = Some t'.
    Proof. reflexivity. Qed.

    Theorem WellTyped_expr_Func : forall g f t',
      WellTyped_expr g (Inj f) t' <->
      typeof_func f = Some t'.
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

  Theorem nth_error_typeof_env : forall (fs : env typD) n,
    nth_error (typeof_env fs) n = match nth_error fs n with
                                    | None => None
                                    | Some x => Some (projT1 x)
                                  end.
  Proof.
    unfold typeof_env; intros.
    rewrite nth_error_map. reflexivity.
  Qed.

End typed.
