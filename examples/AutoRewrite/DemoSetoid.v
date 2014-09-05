Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprD.
Require Import McExamples.AutoRewrite.SetoidRewriteRec.
Require Import McExamples.Simple.Simple.

Set Strict Implicit.

Definition SRrespects (e : expr typ func) (l : RG (expr typ func))
: option (RG (expr typ func)) :=
  match e , l with
    | Inj Lt , RGrespects a (RGrespects b (RGinj (Inj (Eq _)))) =>
      match unify (fun x y => x ?[ eq ] y) a (RGinj (Inj Lt))
          , unify (fun x y => x ?[ eq ] y) b (RGinj (Inj (Eq tyNat)))
      with
        | Some a , Some b => Some (RGrespects a (RGrespects b (RGinj (Inj (Eq tyProp)))))
        | _ , _ => None
      end
    | Inj (Eq t) , RGrespects a (RGrespects b (RGinj (Inj (Eq _)))) =>
      (** unification is problematic here, I really need
       ** a way to maintain a mapping of relation unification
       ** variables to relations
       **)
      match unify (fun x y => x ?[ eq ] y) a (RGinj (Inj (Eq t)))
          , unify (fun x y => x ?[ eq ] y) b (RGinj (Inj (Eq t)))
      with
        | Some a , Some b => Some (RGrespects a (RGrespects b (RGinj (Inj (Eq t)))))
        | _ , _ => None
      end
    | Inj Plus , RGrespects a (RGrespects b (RGinj (Inj (Eq t)))) =>
      (** unification is problematic here, I really need
       ** a way to maintain a mapping of relation unification
       ** variables to relations
       **)
      match unify (fun x y => x ?[ eq ] y) a (RGinj (Inj (Eq t)))
          , unify (fun x y => x ?[ eq ] y) b (RGinj (Inj (Eq t)))
      with
        | Some a , Some b => Some (RGrespects a (RGrespects b (RGinj (Inj (Eq t)))))
        | _ , _ => None
      end
    | _ , _ => None
  end.

Definition SRreflexive (rg : RG (expr typ func)) : option (R (expr typ func)) :=
  match rg with
    | RGany => Some (Rinj (Inj (Eq tyNat))) (* BAD *)
    | RGinj (Inj (Eq t)) => Some (Rinj (Inj (Eq t)))
    | RGinj (Inj Lt) => Some (Rinj (Inj Lt))
    | _ => None
  end.

Let plus_expr : expr typ func := (App (App (Inj Plus) (Var 0)) (Var 1)).

Definition the_rewriter (e : expr typ func) (c : list (RG (expr typ func))) (rg : RG (expr typ func))
: option (expr typ func * list (RG (expr typ func)) * RG (expr typ func)) :=
  match e , rg with
    | Var 0 , RGinj (Inj (Eq tyNat)) =>
      Some (Var 6, c, RGinj (Inj (Eq tyNat)))
    | _ , _ => None
  end.

Eval compute in
    @setoid_rewrite typ func (expr typ func) (fun x y => x ?[ eq ] y)
                    SRrespects SRreflexive the_rewriter
                    plus_expr
                    (RGinj (Inj (Eq tyNat)) :: RGinj (Inj (Eq tyNat)) :: nil)
                    (RGinj (Inj (Eq tyNat))).
