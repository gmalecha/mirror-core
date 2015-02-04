Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.Lambda.Red.
Require MirrorCore.Subst.FMapSubst.
Require Import MirrorCore.RTac.RTac.
Require Import McExamples.Simple.Simple.

Local Instance Expr_expr : Expr _ (expr typ func) := @Expr_expr _ _ _ _ _.
Definition subst :=
  FMapSubst.SUBST.raw (expr typ func).
Local Instance Subst_subst : SubstI.Subst subst (expr typ func)
  := FMapSubst.SUBST.Subst_subst _.
Local Instance SubstUpdate_subst : SubstI.SubstUpdate subst (expr typ func)
  := @FMapSubst.SUBST.SubstUpdate_subst _ _ _ _.


Definition open (e : expr typ func)
: option (@OpenAs typ (expr typ func)) :=
  match e with
    | App (Inj (All t)) e =>
      Some (AsAl t (fun x => beta (App e x)))
    | App (App (Inj Impl) P) Q =>
      Some (AsHy P Q)
    | _ => None
  end.

Let INTRO : rtac typ (expr typ func) := @INTRO _ _ _ _ open.

Let APPLY
: Lemma.lemma typ (expr typ func) (expr typ func) -> rtac typ (expr typ func) :=
  @APPLY typ (expr typ func) _ _ _ _
         (fun _ _ _ => @exprUnify _ _ _ _ _ _ _ _ 10).

Let EAPPLY
: Lemma.lemma typ (expr typ func) (expr typ func) -> rtac typ (expr typ func) :=
  @EAPPLY typ (expr typ func) _ _ _ _
         (fun _ _ _ => @exprUnify _ _ _ _ _ _ _ _ 10).

Let ASSUMPTION : rtac typ (expr typ func) :=
  EASSUMPTION (fun _ _ _ _ x y s => if x ?[ eq ] y then Some s else None).

Definition fAll (t : typ) (P : expr typ func) : expr typ func :=
  App (Inj (All t)) (Abs t P).

Definition fImpl (P Q : expr typ func) : expr typ func :=
  App (App (Inj Impl) P) Q.

Definition fAnd (P Q : expr typ func) : expr typ func :=
  App (App (Inj And) P) Q.


Definition tac : rtac typ (expr typ func) :=
  THEN (REPEAT 10 INTRO)
       (runOnGoals (TRY ASSUMPTION)).

Definition runRTac_empty_goal (tac : rtac typ (expr typ func))
           (goal : expr typ func)  :=
  THENK (@runOnGoals _ _ _ _ tac) (@MINIFY _ _ _ _ _)
        nil nil 0 0 (@TopSubst _ _ nil nil)
        (@GGoal typ (expr typ func) goal).

Definition simple_goal : expr typ func :=
  fAll tyProp (fImpl (Var 0) (Var 0)).

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

Let to_rtacK : rtac typ (expr typ func) -> rtacK typ (expr typ func) :=
  runOnGoals.

(** TODO: How to do a coercion? **)
Local Coercion to_rtacK : rtac >-> rtacK.

Eval compute in
    let goal :=
        fAll tyProp (fAll tyProp
                          (fImpl (Var 0)
                                 (fImpl (Var 1)
                                        (fAnd (Var 0) (Var 1)))))
    in
    runRTac_empty_goal (THEN (REPEAT 10 INTRO)
                             (to_rtacK (THEN (APPLY and_lem)
                                   (to_rtacK (FIRST (ASSUMPTION :: IDTAC :: nil))))))
                       goal.

Eval compute in
    let goal :=
        fAll tyProp (fAll tyProp
                          (fImpl (Var 0)
                                 (fImpl (Var 1)
                                        (fAnd (Var 0) (Var 1)))))
    in
    runRTac_empty_goal (THEN (REPEAT 10 INTRO)
                             (to_rtacK (EAPPLY and_lem))) goal.

Definition random_lem : Lemma.lemma typ (expr typ func) (expr typ func) :=
{| Lemma.vars := tyProp :: tyNat :: tyBool :: tyNat :: nil
 ; Lemma.premises := Var 0 :: App (App (Inj (Eq tyBool)) (App (App (Inj Lt) (Var 1)) (Var 3))) (Var 2) :: nil
 ; Lemma.concl := Var 0
 |}.

Eval compute in
    let goal :=
        fAll tyProp (fAll tyProp
                          (fImpl (Var 0)
                                 (fImpl (Var 1)
                                        (fAnd (Var 0) (Var 1)))))
    in
    runRTac_empty_goal (THEN (REPEAT 10 INTRO)
                             (to_rtacK (EAPPLY random_lem))) goal.
