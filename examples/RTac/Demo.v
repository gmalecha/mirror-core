Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.Red.
Require Import McExamples.Simple.Simple.
Require Import MirrorCore.RTac.CoreSimple.

Definition simple_goal : expr typ func :=
  App (Inj (All tyProp)) (Abs tyProp (App (App (Inj Impl) (Var 0)) (Var 0))).

Definition open (e : expr typ func)
: option ((typ + expr typ func) * expr typ func) :=
  match e with
    | App (Inj (All t)) e =>
      Some (inl t, beta (App e (Var 0)))
    | App (App (Inj Impl) P) Q =>
      Some (inr P, Q)
    | _ => None
  end.

Inductive Ctx :=
| CTop
| CAll : typ -> Ctx -> Ctx
| CEx  : typ -> Ctx -> Ctx
| CHyp : expr typ func -> Ctx -> Ctx.

Fixpoint openGoal' {subst} (g : Goal typ (expr typ func) subst) (ctx : Ctx)
: Ctx * subst * option (expr typ func) :=
  match g with
    | GGoal s e => (ctx,s,e)
    | GAlls t g => openGoal' g (CAll t ctx)
    | GExs  t g => openGoal' g (CEx  t ctx)
    | GHyps h g => openGoal' g (CHyp h ctx)
  end.

Definition openGoal {subst} g := @openGoal' subst g CTop.

Fixpoint closeGoal {subst} (ctx : Ctx) (g : Goal typ (expr typ func) subst)
: Goal typ (expr typ func) subst :=
  match ctx with
    | CTop => g
    | CAll t c => closeGoal c (GAlls t g)
    | CEx t c => closeGoal c (GExs t g)
    | CHyp t c => closeGoal c (GHyps t g)
  end.

Section assumption.
  Context {subst : Type}.
  Variable (check : expr typ func -> expr typ func -> subst -> option subst).

  Fixpoint findHyp s (ctx : Ctx) (g : expr typ func) {struct ctx}
  : option subst :=
    match ctx with
      | CTop => None
      | CAll t ctx' => findHyp s ctx' g
      | CEx  t ctx' => findHyp s ctx' g
      | CHyp h ctx' => match check g h s with
                         | None => findHyp s ctx' g
                         | Some e => Some e
                       end
    end.

  Definition ASSUMPTION : rtac typ (expr typ func) subst :=
    fun g =>
      let '(ctx,s,gl) := openGoal g in
      match gl with
        | None => Some g
        | Some gl => match findHyp s ctx gl with
                       | None => None
                       | Some s => Some (@closeGoal _ ctx (GGoal _ s None))
                     end
      end.
End assumption.

Let INTRO {subst} :=
  INTRO (subst:=subst) (fun f e => substitute_all f 0 e) (@Var typ func) open.

Definition tac subst : rtac typ (expr typ func) subst :=
  THEN INTRO (THEN INTRO (ASSUMPTION (fun x y s => if x ?[ eq ] y then Some s else None))).

Eval compute in fun subst (empty : subst) =>
                  tac subst (@GGoal _ _ _ empty (Some simple_goal)).