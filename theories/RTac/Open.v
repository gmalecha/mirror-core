Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.RTac.Core.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Variable RType_typ : RType typ.
  Variable Expr_expr : Expr RType_typ expr.
  Variable Typ0_Prop : Typ0 _ Prop.
  Variable Subst_subst : Subst subst expr.
  Variable SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst.

  Fixpoint openGoal' (g : Goal typ expr subst) (ctx : Ctx typ expr)
  : Ctx typ expr * subst * option expr :=
    match g with
      | GGoal s e => (ctx,s,Some e)
      | GSolved s => (ctx,s,None)
      | GAll t g => openGoal' g (CAll ctx t)
      | GEx  t g => openGoal' g (CEx  ctx t)
      | GHyp h g => openGoal' g (CHyp ctx h)
    end.

  Definition openGoal g := @openGoal' g CTop.

  Fixpoint closeGoal (ctx : Ctx typ expr) (g : Goal typ expr subst)
  : Goal typ expr subst :=
    match ctx with
      | CTop => g
      | CAll c t => closeGoal c (GAll t g)
      | CEx  c t => closeGoal c (GEx t g)
      | CHyp c h => closeGoal c (GHyp h g)
    end.

  Fixpoint getEnvs' (ctx : Ctx typ expr) (tus tvs : tenv typ)
  : tenv typ * tenv typ :=
    match ctx with
      | CTop => (tus,tvs)
      | CAll ctx' t => getEnvs' ctx' tus (t :: tvs)
      | CEx  ctx' t => getEnvs' ctx' (t :: tus) tvs
      | CHyp ctx' _ => getEnvs' ctx' tus tvs
    end.

  Definition getEnvs (ctx : Ctx typ expr) : tenv typ * tenv typ :=
    let (x,y) := getEnvs' ctx nil nil in
    (x, y).

  Fixpoint countVars' (ctx : Ctx typ expr) acc : nat :=
    match ctx with
      | CTop => acc
      | CAll ctx' t => countVars' ctx' (S acc)
      | CEx  ctx' _
      | CHyp ctx' _ => countVars' ctx' acc
    end.

  Fixpoint countUVars' (ctx : Ctx typ expr) acc : nat :=
    match ctx with
      | CTop => acc
      | CEx  ctx' t => countUVars' ctx' (S acc)
      | CAll ctx' _
      | CHyp ctx' _ => countUVars' ctx' acc
    end.


  Definition countVars ctx := countVars' ctx 0.
  Definition countUVars ctx := countUVars' ctx 0.

(*
  Eval compute in fun t u v a b =>
      let '(x,_,_) := openGoal (GAlls t (GAlls u (GAlls v (GGoal a b)))) in
      getEnvs x.
*)


(**
  Definition finish : rtac typ expr subst :=
    fun g =>
      let '(ctx,s,gl) := openGoal g in
      let (tus,tvs) := getEnvs ctx in
      let (ctx',s) := reduceGoal ctx s (length tus) (length tvs) in
      Some (closeGoal ctx' (GGoal s None)).
**)


End parameterized.