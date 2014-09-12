Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.Lambda.Red.
Require MirrorCore.Subst.FMapSubst.
Require Import MirrorCore.RTac.RTac.
Require Import McExamples.Simple.Simple.

Local Instance Expr_expr : Expr _ (expr typ func) := Expr_expr.
Definition subst :=
  FMapSubst.SUBST.raw (expr typ func).
Local Instance Subst_subst : SubstI.Subst subst (expr typ func)
  := FMapSubst.SUBST.Subst_subst _.
Local Instance SubstUpdate_subst : SubstI.SubstUpdate subst (expr typ func)
  := FMapSubst.SUBST.SubstUpdate_subst _.
eapply instantiate.
Defined.


Definition open (e : expr typ func)
: option (   ((typ * (expr typ func -> expr typ func))
           + (expr typ func * expr typ func))) :=
  match e with
    | App (Inj (All t)) e =>
      Some (inl (t, fun x => beta (App e x)))
    | App (App (Inj Impl) P) Q =>
      Some (inr (P, Q))
    | _ => None
  end.

Let INTRO :=
  INTRO (subst:=subst) (@Var typ func) open.

Let APPLY := @APPLY typ (expr typ func) subst _ _ _ _
                    (@vars_to_uvars _ _)
                    (fun tus tvs n l r t s =>
                       @exprUnify _ _ _ _ _ _ _ _ 10 tus tvs n s l r t)
                    (@instantiate _ _).
Let ASSUMPTION : rtac typ (expr typ func) subst :=
  ASSUMPTION _ (fun x y s => if x ?[ eq ] y then Some s else None).

Definition fAll (t : typ) (P : expr typ func) : expr typ func :=
  App (Inj (All t)) (Abs t P).

Definition fImpl (P Q : expr typ func) : expr typ func :=
  App (App (Inj Impl) P) Q.

Definition fAnd (P Q : expr typ func) : expr typ func :=
  App (App (Inj And) P) Q.


Definition tac : rtac typ (expr typ func) subst :=
  THEN (REPEAT 10 INTRO)
       (TRY ASSUMPTION).


Definition simple_goal : expr typ func :=
  fAll tyProp (fImpl (Var 0) (Var 0)).

Definition runRTac_empty_goal (tac : rtac typ (expr typ func) subst)
           (goal : expr typ func)  :=
  runRTac tac (@GGoal typ (expr typ func) subst (@empty _ _ _) (Some goal)).

Eval compute in
    runRTac_empty_goal tac simple_goal.

Definition simple_goal2 : expr typ func :=
  fAll tyProp (fImpl (Var 0) (fAll tyProp (Var 0))).

Eval compute in runRTac_empty_goal tac simple_goal2.

Definition simple_goal3 : expr typ func :=
  fAll tyProp (fImpl (Var 0) (fAll tyProp (Var 1))).

Eval compute in runRTac_empty_goal tac simple_goal3.

Definition and_lem : Lemma.lemma typ (expr typ func) (expr typ func) :=
{| Lemma.vars := tyProp :: tyProp :: nil
 ; Lemma.premises := Var 0 :: Var 1 :: nil
 ; Lemma.concl := App (App (Inj And) (Var 0)) (Var 1)
 |}.

Eval compute in
    let goal :=
        fAll tyProp (fAll tyProp
                          (fImpl (Var 0)
                                 (fImpl (Var 1)
                                        (fAnd (Var 0) (Var 1)))))
    in
    runRTac_empty_goal (THEN (REPEAT 10 INTRO)
                             (APPLY and_lem ASSUMPTION)) goal.
