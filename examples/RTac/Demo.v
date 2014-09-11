Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.Red.
Require Import McExamples.Simple.Simple.
Require Import MirrorCore.RTac.RTac.

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

Let INTRO {subst} :=
  INTRO (subst:=subst) (@Var typ func) open.

Definition tac subst : rtac typ (expr typ func) subst :=
  THEN (REPEAT 10 INTRO)
       (TRY (ASSUMPTION (fun x y s => if x ?[ eq ] y then Some s else None))).

Definition fAll (t : typ) (P : expr typ func) : expr typ func :=
  App (Inj (All t)) (Abs t P).
Definition fImpl (P Q : expr typ func) : expr typ func :=
  App (App (Inj Impl) P) Q.

Definition simple_goal : expr typ func :=
  fAll tyProp (fImpl (Var 0) (Var 0)).

Eval compute in fun subst (empty : subst) =>
                  tac subst (@GGoal _ _ _ empty (Some simple_goal)).

Definition simple_goal2 : expr typ func :=
  fAll tyProp (fImpl (Var 0) (fAll tyProp (Var 0))).

Eval compute in fun subst (empty : subst) =>
                  tac subst (@GGoal _ _ _ empty (Some simple_goal2)).

Definition simple_goal3 : expr typ func :=
  fAll tyProp (fImpl (Var 0) (fAll tyProp (Var 1))).

Eval compute in fun subst (empty : subst) =>
                  tac _ (@GGoal _ _ _ empty (Some simple_goal3)).
