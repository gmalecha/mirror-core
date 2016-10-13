Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.Compat.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprD.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.RewriteRelations.
Require Import MirrorCore.Lambda.RewriteStrat.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.Lambda.Rewrite.HintDbs.
Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.RTac.IdtacK.
Require Import MirrorCore.RTac.Intro.
Require Import MirrorCore.RTac.Then.
Require Import MirrorCore.RTac.RunOnGoals.
Require Import MirrorCore.RTac.PApply.
Require Import MirrorCore.CTypes.CoreTypes.
Require Import MirrorCore.Polymorphic.
Require Import MirrorCore.PLemma.

Require Import McExamples.PolyRewrite.MSimple.
Require Import McExamples.PolyRewrite.MSimpleReify.

Existing Instance RType_typ.
Existing Instance Expr.Expr_expr.
Existing Instance Expr.ExprOk_expr.
Existing Instance Typ2_Fun.
Existing Instance Typ2Ok_Fun.

Require Import MirrorCore.VariablesI.
Require Import MirrorCore.Lambda.ExprVariables.

Global Instance ExprVar_expr : ExprVar (expr typ func) := _.
Global Instance ExprVarOk_expr : ExprVarOk ExprVar_expr := _.

Global Instance ExprUVar_expr : ExprUVar (expr typ func) := _.
Global Instance ExprUVarOk_expr : ExprUVarOk ExprUVar_expr := _.

Definition subst : Type :=
  FMapSubst.SUBST.raw (expr typ func).
Global Instance SS : SubstI.Subst subst (expr typ func) :=
  @FMapSubst.SUBST.Subst_subst _.
Global Instance SU : SubstI.SubstUpdate subst (expr typ func) :=
  @FMapSubst.SUBST.SubstUpdate_subst _ _ _ _.
Global Instance SO : @SubstI.SubstOk _ _ _ _ _ SS :=
  @FMapSubst.SUBST.SubstOk_subst typ RType_typ (expr typ func) _.
Global Instance SUO : @SubstI.SubstUpdateOk _ _ _ _ _ _ SU SO :=  @FMapSubst.SUBST.SubstUpdateOk_subst typ RType_typ (expr typ func) _ _.

Definition fintro (e : expr typ func) : option (@OpenAs typ (expr typ func)) :=
  match e with
  | App (Inj (Ex t)) P => Some (AsEx t (fun x => beta (App P x)))
  | App (Inj (All t)) P => Some (AsAl t (fun x => beta (App P x)))
  | App (App (Inj Impl) P) Q => Some (AsHy P Q)
  | _ => None
  end.

Definition INTRO := @INTRO typ (expr typ func) ExprVar_expr ExprUVar_expr fintro.


Lemma forall_exists_eq {A : Type} : forall x : A, exists y, x = y.
Proof.
  intros.
  exists x. reflexivity.
Qed.

Definition lem_forall_exists_eq : polymorphic typ 1 (Lemma.lemma typ (expr typ func) (expr typ func)) :=
  Eval unfold Lemma.add_var, Lemma.add_prem , Lemma.vars , Lemma.concl , Lemma.premises in
  <:: @forall_exists_eq ::>.

Definition p_lem_forall_exists_eq : PolyLemma typ (expr typ func) (expr typ func) :=
 {| p_n := 1;
    p_lem := lem_forall_exists_eq;
    p_tc := fun _ => true
 |}.

Print lem_forall_exists_eq.

Let tyBNat := CoreTypes.tyBase0 tyNat.
Let tyBBool := CoreTypes.tyBase0 tyBool.

Definition fAnd a b : expr typ func := App (App (Inj MSimple.And) a) b.
Definition fOr a b : expr typ func := App (App (Inj MSimple.And) a) b.
Definition fAll t P : expr typ func := App (Inj (MSimple.All t)) (Abs t P).
Definition fEx t P : expr typ func := App (Inj (MSimple.Ex t)) (Abs t P).
Definition fEq t : expr typ func := (Inj (MSimple.Eq t)).
Definition fImpl : expr typ func := (Inj MSimple.Impl).
Definition mkEq t a b : expr typ func := App (App (fEq t) a) b.
Definition fN n : expr typ func := Inj (MSimple.N n).

Require Import MirrorCore.RTac.PApply.
Require Import MirrorCore.Lambda.ExprUnify_simple.
About func.

Definition PAPPLY (plem : PolyLemma typ (expr typ func) (expr typ func)) :=
  PAPPLY
    (fun subst SS SU tus tvs n l r t s =>
              @exprUnify subst typ func RType_typ RSym_func Typ2_Fun
                         SS SU 10 tus tvs n l r t s) func_unify plem.

Eval vm_compute in
    (THEN INTRO (runOnGoals (PAPPLY p_lem_forall_exists_eq)))
      (CTop nil nil)
      (TopSubst _ nil nil)
      (fAll tyBNat (fEx tyBNat (mkEq tyBNat (Var 1) (Var 0)))).
