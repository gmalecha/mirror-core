Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprD.
Require Import McExamples.AutoRewrite.AutoSetoidRewrite.
Require Import McExamples.Simple.Simple.

Set Implicit Arguments.
Set Strict Implicit.

Require Import McExamples.Simple.Simple.

Let Rbase := expr typ func.

Definition m (T : Type) : Type :=
  rsubst Rbase -> option (T * rsubst Rbase).

Definition rg_bind {T U} (a : m T) (b : T -> m U) : m U :=
  fun s => match a s with
             | None => None
             | Some (val,s') => b val s'
           end.
Definition rg_fail {T} : m T := fun _ => None.
Definition rg_ret {T} (v : T) : m T := fun s => Some (v, s).
Definition rg_plus {T} (l r : m T) : m T :=
  fun s =>
    let v := l s in
    match v with
      | None => r s
      | Some _ => v
    end.

Definition SRrespects (e : expr typ func) (l : RG (expr typ func))
: m (RG (expr typ func)) :=
  match e , l with
    | Inj Lt , RGrespects a (RGrespects b (RGinj (Inj (Eq _)))) =>
      rg_bind
        (unifyRG (fun x y => x ?[ eq ] y) a (RGinj (Inj Lt)))
        (fun a =>
           rg_bind
             (unifyRG (fun x y => x ?[ eq ] y) b (RGinj (Inj (Eq tyNat))))
             (fun b =>
                rg_ret (RGrespects a (RGrespects b (RGinj (Inj (Eq tyProp)))))))
    | Inj (Eq t) , RGrespects a (RGrespects b (RGinj (Inj (Eq _)))) =>
      rg_bind
        (unifyRG (fun x y => x ?[ eq ] y) a (RGinj (Inj (Eq t))))
        (fun a =>
           rg_bind
             (unifyRG (fun x y => x ?[ eq ] y) b (RGinj (Inj (Eq t))))
             (fun b =>
                rg_ret (RGrespects a (RGrespects b (RGinj (Inj (Eq t)))))))
    | Inj Plus , RGrespects a (RGrespects b (RGinj (Inj (Eq t)))) =>
      rg_bind
        (unifyRG (fun x y => x ?[ eq ] y) a (RGinj (Inj (Eq t))))
        (fun a =>
           rg_bind
             (unifyRG (fun x y => x ?[ eq ] y) b (RGinj (Inj (Eq t))))
             (fun b =>
                rg_ret (RGrespects a (RGrespects b (RGinj (Inj (Eq t)))))))
    | _ , _ => rg_fail
  end.

Let plus_expr : expr typ func := (App (App (Inj Plus) (Inj (N 0))) (Inj (N 5))).

Definition the_rewriter (e : expr typ func) (c : list (RG (expr typ func)))
           (rg : RG (expr typ func))
: m (expr typ func) :=
  match e with
    | Inj (N 0) =>
      rg_bind (unifyRG (fun x y => x ?[ eq ] y) rg (RGinj (Inj (Eq tyNat))))
              (fun _ =>
                 rg_ret (Inj (N 1)))
    | Inj _ => rg_bind (SRrespects e rg) (fun _ => rg_ret e)
    | _ => rg_fail
  end.

Definition rewriter (e : expr typ func)
           (vars : list (RG Rbase))
           (r : RG Rbase) : m (expr typ func) :=
  the_rewriter e vars r.

Definition rewriter_default (e : expr typ func)
           (vars : list (RG Rbase))
           (rg : RG Rbase) : m (expr typ func) :=
  match rg with
    | RGvar n =>
      let type := tyNat in
      rg_bind
        (unifyRG (fun x y => x ?[ eq ] y) rg (RGinj (Inj (Eq type))))
        (fun _ => rg_ret e)
    | RGinj (Inj (Eq _)) => rg_ret e
    | _ => rg_fail
  end.

Eval vm_compute in
    @setoid_rewrite typ func (expr typ func)
                    (fun x y => x ?[ eq ] y)
                    rewriter
                    rewriter_default
                    (fun e _ _ rs => Some (e,rs))
                    plus_expr
                    (RGinj (Inj (Eq tyNat)) :: RGinj (Inj (Eq tyNat)) :: nil)
                    (RGinj (Inj (Eq tyNat))) (@rsubst_empty _).