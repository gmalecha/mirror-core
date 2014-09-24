Require Import Coq.Lists.List.
Require Import ExtLib.Data.HList.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.EnvI.

Set Implicit Arguments.
Set Strict Implicit.

Section with_Expr.
  Variable typ : Type.
  Variable RType_typ : RType typ.
  Variable expr : Type.
  Variable Expr_expr : @Expr typ _ expr.

  Class ExprVar : Type :=
  { Var : nat -> expr
  ; mentionsV : nat -> expr -> bool
  }.

  Class ExprVarOk (EV : ExprVar) : Prop :=
  { Var_exprD'
    : forall tus tvs v t,
        match exprD' tus tvs (Var v) t with
          | None =>
            nth_error tvs v = None \/
            exists t', nth_error tvs v = Some t' /\ ~Rty t t'
          | Some vD =>
            exists get,
            nth_error_get_hlist_nth typD tvs v = Some (@existT _ _ t get) /\
            forall us vs,
              get vs = vD us vs
        end
  ; exprD'_strengthenV_single
    : forall tus tvs e t t' val,
      mentionsV (length tvs) e = false ->
      exprD' tus (tvs ++ t :: nil) e t' = Some val ->
      exists val',
        exprD' tus tvs e t' = Some val' /\
        forall us vs u,
          val us (hlist_app vs (Hcons u Hnil)) = val' us vs
  ; mentionsV_Var : forall v v', mentionsV v (Var v') = true <-> v = v'
  }.

  Class ExprUVar : Type :=
  { UVar : nat -> list expr -> expr
  ; mentionsU : nat -> expr -> bool
  }.

  Class ExprUVarOk (EV : ExprUVar) : Prop :=
  { UVar_exprD'
    : forall tus tvs v es t,
        match exprD' tus tvs (UVar v es) t with
          | None =>
            match nth_error tus v with
              | None => True
              | Some t' =>
                ~Rty t t'.(vtyp) \/
                ~Forall2 (fun t e => exprD' tus tvs e t = None -> False) t'.(cctx) es
            end
          | Some vD =>
            exists get,
            nth_error_get_hlist_nth typD tvs v = Some (@existT _ _ t get) /\
            forall us vs,
              get vs = vD us vs
        end
  ; exprD'_strengthenU_single
    : forall tus tvs e t t' val,
      mentionsU (length tus) e = false ->
      exprD' (tus ++ t :: nil) tvs e t' = Some val ->
      exists val',
        exprD' tus tvs e t' = Some val' /\
        forall us vs u,
          val (hlist_app us (Hcons u Hnil)) vs = val' us vs
  ; mentionsU_UVar : forall u es u',
                       mentionsU u (UVar u' es) = true <->
                       (u = u' \/ exists e, In e es /\ mentionsU u e = true)
  }.

End with_Expr.

Arguments ExprVar expr : rename.
Arguments ExprUVar expr : rename.
Arguments ExprVarOk {typ _ expr _} _ : rename.
Arguments ExprUVarOk {typ _ expr _} _ : rename.
