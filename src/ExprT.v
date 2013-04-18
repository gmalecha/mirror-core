(* A type system for Expr
 * This achieves a phase split between the 'well-formedness' of expressions
 * and their meaning
 *)
Require Import List.
Require Import ExtLib.Data.HList.
Require Import MirrorCore.ExprCore.

Set Implicit Arguments.
Set Strict Implict.

Section typed.
  Variable ts : types.

  Definition well_typed_func (tf : tfunction) (f : function ts) : bool :=
    typ_eqb tf (ftype f).

  Definition typeof_funcs : functions ts -> tfunctions :=
    map (@ftype _).

  Fixpoint well_typed_funcs (tfs : tfunctions) (fs : functions ts) : bool :=
    match tfs , fs with
      | nil , nil => true
      | tf :: tfs , f :: fs =>
        if well_typed_func tf f then well_typed_funcs tfs fs else false
      | _ , _ => false
    end.

  Definition typeof_env : env ts -> tenv :=
    map (@projT1 _ _).

  Fixpoint well_typed_env (tes : tenv) (es : env ts) : bool :=
    match tes , es with
      | nil , nil => true
      | t :: tes , e :: es => 
        if typ_eqb t (projT1 e) then well_typed_env tes es else false
      | _ , _ => false
    end.      

  Variable fs : tfunctions.
  Variable uvars : tenv.

  Fixpoint typeof_expr (var_env : tenv) (e : expr ts) : option typ :=
    match e with
      | Const t' _ => Some t'
      | Var x  => nth_error var_env x
      | UVar x => nth_error uvars x 
      | Func f ts =>
        match nth_error fs f with
          | None => None
          | Some r => Some (instantiate_typ ts r)
        end
      | App e es =>
        match typeof_expr var_env e with
          | None => None
          | Some tf => type_of_apply tf (map (typeof_expr var_env) es)
        end
      | Abs t e =>
        match typeof_expr (t :: var_env) e with
          | None => None
          | Some t' => Some (tvArr t t')
        end
    end.

  Definition WellTyped_expr (var_env : tenv) (e : expr ts) (t : typ) : Prop :=
    typeof_expr var_env e = Some t.
  
End typed.

Require Import ExtLib.Tactics.Consider.

Theorem typ_eq_odec_None : forall t t', 
  typ_eq_odec t t' = None -> t <> t'.
Proof.
Admitted.

Theorem typ_eq_odec_None_refl : forall t,
  typ_eq_odec t t = None -> False.
Proof.
  intros. apply typ_eq_odec_None in H. auto.
Qed.

Theorem typ_eq_odec_Some_refl : forall t,
  typ_eq_odec t t = Some refl_equal.
Proof.
Admitted.

Theorem exprD_typof_expr_iff : forall ts (fs : functions ts) uenv venv e t,
  WellTyped_expr (typeof_funcs fs) (typeof_env uenv) (typeof_env venv) e t ->
  exists v, exprD fs uenv venv e t = Some v.
Proof.
  unfold exprD, WellTyped_expr. intros.
  cut (projT1 (split_env venv) = typeof_env venv).
  destruct (split_env venv); simpl in *; intros; subst.
  generalize dependent t; generalize dependent venv. 
  induction e; simpl; intros;
    repeat match goal with
             | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
             | [ H : typ_eq_odec _ _ = None |- _ ] => 
               apply typ_eq_odec_None in H
             | |- context [ match ?X with _ => _ end ] =>
               match X with
                 | match _ with _ => _ end => fail 1
                 | _ => consider X; intros
               end
           end; try solve [ eauto | exfalso; auto ].
  { revert H0. 
    match goal with
      | |- match _ with _ => _ end ?X = _ -> _ =>
        generalize X
    end.
    pattern (nth_error (typeof_env venv) v) at 2 3.
    rewrite H. rewrite typ_eq_odec_Some_refl.
    intros. congruence. }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
Qed.