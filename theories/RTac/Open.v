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

  Inductive Ctx :=
  | CTop
  | CAll : typ -> Ctx -> Ctx
  | CEx  : typ -> Ctx -> Ctx
  | CHyp : expr -> Ctx -> Ctx.

  Fixpoint openGoal' (g : Goal typ expr subst) (ctx : Ctx)
  : Ctx * subst * option expr :=
    match g with
      | GGoal s e => (ctx,s,e)
      | GAlls t g => openGoal' g (CAll t ctx)
      | GExs  t g => openGoal' g (CEx  t ctx)
      | GHyps h g => openGoal' g (CHyp h ctx)
    end.

  Definition openGoal g := @openGoal' g CTop.

  Fixpoint closeGoal (ctx : Ctx) (g : Goal typ expr subst)
  : Goal typ expr subst :=
    match ctx with
      | CTop => g
      | CAll t c => closeGoal c (GAlls t g)
      | CEx t c => closeGoal c (GExs t g)
      | CHyp t c => closeGoal c (GHyps t g)
    end.
End parameterized.