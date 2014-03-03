Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.EnvI.

Set Implicit Arguments.
Set Strict Implicit.

Section subst.
  Variable T : Type.
  (** the [expr] type requires a notion of unification variable **)
  Variable expr : Type.
  Let uvar : Type := nat.

  (** I should be able to eliminate subst, but I need to express
   ** the fact that terms returned from [lookup] are fully instantiated.
   ** At the moment, there is no way to state "fully instantiated"
   ** because there is no function over [expr]
   **)

  Class Subst :=
  { set : uvar -> expr -> T -> option T
  ; lookup : uvar -> T -> option expr
  ; empty : T
  }.

  Variable typ : Type.
  Variable typD : list Type -> typ -> Type.
  Variable Expr_expr : Expr typD expr.

  Class SubstOk (S : Subst) : Type :=
  { substD : EnvI.env typD -> EnvI.env typD -> T -> Prop
  ; WellTyped_subst : EnvI.tenv typ -> EnvI.tenv typ -> T -> Prop
  ; substD_empty : forall u v, substD u v empty
  ; WellTyped_empty : forall u v, WellTyped_subst u v empty
  ; WellTyped_lookup : forall u v s uv e,
      WellTyped_subst u v s ->
      lookup uv s = Some e ->
      exists t,
        nth_error u uv = Some t /\
        Safe_expr u v e t
  ; substD_lookup : forall u v s uv e,
      lookup uv s = Some e ->
      substD u v s ->
      exists val,
        nth_error u uv = Some val /\
        exprD u v e (projT1 val) = Some (projT2 val)
  ; WellTyped_set : forall uv e s s' (u v : tenv typ) t,
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
  }.

  Variable Subst_subst : Subst.
  Variable SubstOk_subst : SubstOk Subst_subst.

  (** maybe [mentionsU] should be part of [Expr]? **)
  Variable mentionsU : uvar -> expr -> bool.

  Class NormalizedSubstOk : Type :=
  { lookup_normalized : forall s e u,
      lookup u s = Some e ->
      forall u' e',
        lookup u' s = Some e' ->
        mentionsU u' e = false
  }.


  Definition Subst_Extends (a b : T) : Prop :=
    forall u v, substD u v b -> substD u v a.

End subst.
