Require Import List.
Require Import Relations.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.EnvI.

Set Implicit Arguments.
Set Strict Implicit.

Section subst.
  Variable T : Type.
  Variable expr : Type.
  Let uvar : Type := nat.

  Class Subst :=
  { set : uvar -> expr -> T -> option T
  ; lookup : uvar -> T -> option expr
  ; subst : T -> expr -> expr
  ; empty : T
(*  ; dropRange : uvar -> nat -> T -> option (T * list expr) *)
  }.

  Variable typ : Type.
  Variable typD : list Type -> typ -> Type.
  Variable Expr_expr : Expr typD expr.

  Class SubstOk (S : Subst) : Type :=
  { substD : EnvI.env typD -> EnvI.env typD -> T -> Prop
  ; WellTyped_subst : EnvI.tenv typ -> EnvI.tenv typ -> T -> Prop
  ; substD_empty : forall u v, substD u v empty
  ; WellTyped_empty : forall u v, WellTyped_subst u v empty
  ; substD_subst : forall u v s e t,
      substD u v s ->
      exprD u v e t = exprD u v (subst s e) t
  ; WellTyped_subst_lookup : forall u v s uv e t,
      WellTyped_subst u v s ->
      nth_error u uv = Some t ->
      lookup uv s = Some e ->
      Safe_expr u v e t
  ; substD_lookup : forall u v s uv e,
      lookup uv s = Some e ->
      substD u v s ->
      exists val,
        nth_error u uv = Some val /\
        exprD u v e (projT1 val) = Some (projT2 val)
  ; WellTyped_subst_set : forall uv e s s' (u v : tenv typ) t,
      WellTyped_subst u v s ->
      nth_error u uv = Some t ->
      Safe_expr u v e t ->
      set uv e s = Some s' ->
      WellTyped_subst u v s'
  ; substD_set : forall uv e s s' u v,
      substD u v s' ->
      lookup uv s = None ->
      set uv e s = Some s' ->
      substD u v s /\
      (forall tv, nth_error u uv = Some tv ->
                  exprD u v e (projT1 tv) = Some (projT2 tv))
(*
  ; extractRange_ok : forall u u' v rvs uv cnt s s' r,
      dropRange uv cnt s = Some (s', r) ->
      substD (u ++ rvs ++ u') v s ->
      length r = cnt /\
      substD (u ++ u') v s' /\
      forall n x e,
        nth_error rvs n = Some x ->
        nth_error r n = Some e ->
        exprD (u ++ u') v e (projT1 x) = Some (projT2 x)
*)
  }.

  Variable Subst_subst : Subst.
  Variable SubstOk_subst : SubstOk Subst_subst.

  Definition Subst_Extends (a b : T) : Prop :=
    forall u v, substD u v b -> substD u v a.

  (** the [expr] type requires a notion of unification variable **)

End subst.
