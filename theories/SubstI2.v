Require Import Coq.Lists.List.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.EnvI.

Set Implicit Arguments.
Set Strict Implicit.

Section subst.
  Variable T : Type.
  (** the [expr] type requires a notion of unification variable **)
  Variable typ : Type.
  Variable typD : list Type -> typ -> Type.
  Variable expr : Type.
  Variable Expr_expr : Expr typD expr.

  Let uvar : Type := nat.

  Class Subst :=
  { lookup : uvar -> T -> option expr
  ; domain : T -> list uvar
  }.

  Class SubstUpdate :=
  { set : uvar -> expr -> T -> option T (** TODO: Should this be typed? **)
  ; pull : uvar -> nat -> T -> option T
  ; empty : T
  }.

  Class SubstOk (S : Subst) : Type :=
  { WellFormed_subst : T -> Prop
  ; WellTyped_subst : EnvI.tenv typ -> EnvI.tenv typ -> T -> Prop
  ; substD : EnvI.env typD -> EnvI.env typD -> T -> Prop
  ; substD_WellTyped : forall u v s,
      WellFormed_subst s ->
      substD u v s ->
      WellTyped_subst (typeof_env u) (typeof_env v) s
  ; WellTyped_lookup : forall u v s uv e,
      WellFormed_subst s ->
      WellTyped_subst u v s ->
      lookup uv s = Some e ->
      exists t,
        nth_error u uv = Some t /\
        Safe_expr u v e t
  ; substD_lookup : forall u v s uv e,
      WellFormed_subst s ->
      lookup uv s = Some e ->
      substD u v s ->
      exists val,
        nth_error u uv = Some val /\
        exprD u v e (projT1 val) = Some (projT2 val)
  ; WellFormed_domain : forall s ls,
      WellFormed_subst s ->
      domain s = ls ->
      (forall n, In n ls <-> lookup n s <> None)
  }.

  Class SubstUpdateOk (S : Subst) (SU : SubstUpdate) (SOk : SubstOk S) :=
  { WellFormed_empty : WellFormed_subst empty
  ; substD_empty : forall u v, substD u v empty
  ; WellTyped_empty : forall u v, WellTyped_subst u v empty
  ; WellFormed_set : forall uv e s s',
      WellFormed_subst s ->
      set uv e s = Some s' ->
      WellFormed_subst s'
  ; WellTyped_set : forall uv e s s' (u v : tenv typ) t,
      WellFormed_subst s ->
      WellTyped_subst u v s ->
      nth_error u uv = Some t ->
      Safe_expr u v e t ->
      set uv e s = Some s' ->
      WellTyped_subst u v s'
  ; substD_set : forall uv e s s' u v,
      WellFormed_subst s ->
      substD u v s' ->
      lookup uv s = None ->
      set uv e s = Some s' ->
      substD u v s /\
      (forall tv, nth_error u uv = Some tv ->
                  exprD u v e (projT1 tv) = Some (projT2 tv))
  ; WellFormed_pull : forall s s' u n,
      WellFormed_subst s ->
      pull u n s = Some s' ->
      WellFormed_subst s'
  ; WellTyped_pull : forall tus tus' tvs u s s',
      WellFormed_subst s ->
      pull u (length tus') s = Some s' ->
      WellTyped_subst (tus ++ tus') tvs s ->
      WellTyped_subst tus tvs s'
  ; substD_pull : forall us us' vs u s s',
      WellFormed_subst s ->
      substD (us ++ us') vs s ->
      pull u (length us') s = Some s' ->
      substD us vs s'
  }.

  Variable Subst_subst : Subst.
  Variable SubstOk_subst : SubstOk Subst_subst.

  (** maybe [mentionsU] should be part of [Expr]? **)
  Variable mentionsU : uvar -> expr -> bool.

  Class NormalizedSubstOk : Type :=
  { lookup_normalized : forall s e u,
      WellFormed_subst s ->
      lookup u s = Some e ->
      forall u' e',
        lookup u' s = Some e' ->
        mentionsU u' e = false
  }.

  Definition Subst_Extends (a b : T) : Prop :=
    forall u v,
      substD u v b ->
      substD u v a.

End subst.
