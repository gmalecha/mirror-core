Require Import Coq.Lists.List.
Require Import ExtLib.Data.HList.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.

Section definitions.
  Variables typ : Type.
  Variable expr : tenv typ -> tenv typ -> typ -> Type.
  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr _ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.

  (** instantiate = substituteU **)

  Definition subst_fn (tus tvs : tenv typ) : Type
  := forall (n : nat) (t : typ), option (expr tus tvs t).

  (** instantiate **)
  Variable instantiate
  : forall tus tvs t,
      subst_fn tus tvs ->
      forall tvs',
      expr tus (tvs' ++ tvs) t -> expr tus (tvs' ++ tvs) t.

  Definition sem_preserves_if tus tvs
             (P : hlist _ tus -> hlist _ tvs -> Prop)
             (f : subst_fn tus tvs) : Prop :=
    forall u t (e : expr tus tvs t) get,
      f u t = Some e ->
      nth_error_get_hlist_nth _ tus u = Some (@existT _ _ t get) ->
      exists eD,
        exprD' tus tvs t e = Some eD /\
        forall us vs,
          P us vs ->
          get us = eD us vs.

(*
  Definition instantiate_mentionsU : Prop :=
    forall tus tvs t f n e u,
      mentionsU tus tvs t u (instantiate f n e) = true <-> (** do i need iff? **)
      (   (f u = None /\ mentionsU u e = true)
       \/ exists u' e',
            f u' = Some e' /\
            mentionsU u' e = true /\
            mentionsU u e' = true).
*)

  Check instantiate.

  Definition exprD'_instantiate : Prop :=
    forall tus tvs tvs' t f e eD P,
      sem_preserves_if tus tvs P f ->
      exprD' tus (tvs' ++ tvs) t e = Some eD ->
      exists eD',
        exprD' tus (tvs' ++ tvs) t (@instantiate tus tvs t f tvs' e) = Some eD' /\
        forall us vs vs',
          P us vs ->
          eD us (hlist_app vs' vs) = eD' us (hlist_app vs' vs).
End definitions.

Arguments sem_preserves_if {typ expr RType Expr} _ _ _ _ : rename.
