Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprD.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.AutoSetoidRewrite.
Require Import McExamples.Simple.Simple.

Set Implicit Arguments.
Set Strict Implicit.

Definition fAnd a b : expr typ func := App (App (Inj Simple.And) a) b.
Definition fOr a b : expr typ func := App (App (Inj Simple.And) a) b.
Definition fAll t P : expr typ func := App (Inj (Simple.All t)) (Abs t P).
Definition fEx t P : expr typ func := App (Inj (Simple.Ex t)) (Abs t P).
Definition fEq_nat a b : expr typ func := App (App (Inj (Simple.Eq tyNat)) a) b.
Definition fN n : expr typ func := Inj (Simple.N n).

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

Definition goal : expr typ func :=
  fAnd (fEx tyNat (fEq_nat (Var 0) (fN 3)))
       (fEx tyNat (fEq_nat (Var 0) (fN 7))).

Theorem pull_ex_nat_and_left
: forall T P Q, ((exists n : T, P n) /\ Q) = (exists n, P n /\ Q).
Admitted.

Theorem pull_ex_nat_and_right
: forall T P Q, (Q /\ (exists n : T, P n)) = (exists n, Q /\ P n).
Admitted.

Definition rewrite_exs (e : expr typ func) (rvars : list (RG (expr typ func)))
           (rg : RG (expr typ func)) : m (expr typ func) :=
  match e with
    | App (App (Inj Simple.And) (App (Inj (Simple.Ex t)) P)) Q =>
      rg_bind
        (unifyRG rel_dec rg (RGinj (Inj (Simple.Eq tyProp))))
        (fun _ =>
           rg_ret (App (Inj (Simple.Ex t)) (Abs t (App (App (Inj Simple.And) (App P (Var 0))) Q))))
    | App (App (Inj Simple.And) Q) (App (Inj (Simple.Ex t)) P) =>
      rg_bind
        (unifyRG rel_dec rg (RGinj (Inj (Simple.Eq tyProp))))
        (fun _ =>
           rg_ret (App (Inj (Simple.Ex t)) (Abs t (App (App (Inj Simple.And) Q) (App P (Var 0))))))
    | _ => rg_fail
  end.

Definition respects : list (expr typ func * R Rbase * expr typ func) :=
  map (fun xy => let '(x,y) := xy in (x,y,x))
      ((Inj Simple.And, Rrespects (Rinj (Inj (Eq tyProp))) (Rrespects (Rinj (Inj (Eq tyProp))) (Rinj (Inj (Eq tyProp))))) ::
       (Inj (Simple.Ex tyNat), Rrespects (Rrespects (Rinj (Inj (Eq tyNat))) (Rinj (Inj (Eq tyProp)))) (Rinj (Inj (Eq tyProp))))

 :: nil).

Definition rewrite_respects := fromRewrites rel_dec respects.

Definition rw_type := expr typ func -> list (RG (expr typ func))
                      -> RG (expr typ func) -> m (expr typ func).

Section interleave.
  Variables (rw rw' : rw_type -> rw_type).

  Fixpoint interleave (n : nat)
           (e : expr typ func) (rvars : list (RG (expr typ func)))
           (rg : RG (expr typ func)) : m (expr typ func) :=
    match n with
      | 0 => rg_fail
      | S n => rw (fun rs => rw' (fun e rvars rg rs => interleave n e rvars rg rs) rs) e rvars rg
    end.
End interleave.



Fixpoint rw_fix (n : nat)
  (rw : rw_type -> rw_type)
  (e : expr typ func) (rvars : list (RG Rbase)) (rg : RG Rbase)
  (rs : rsubst Rbase)
: option (expr typ func * rsubst Rbase) :=
  match n with
    | 0 => Some (e,rs)
    | S n => rw (fun e rvars rg rs => rw_fix n rw e rvars rg rs) e rvars rg rs
  end.

Definition quant_pull (e : expr typ func) : expr typ func :=
  match
    rw_fix 10 (@setoid_rewrite typ func (expr typ func)
                     rel_dec
                     rewrite_exs rewrite_respects)
      e nil (RGinj (Inj (Eq tyProp)))
      (rsubst_empty _)
  with
    | None => e
    | Some (e,_) => e
  end.


(*
Require Import MirrorCore.Lambda.AppN.
(** I'm only pulling one quantifier.
 ** What do I need to instantiate with?
 **)
Definition quant_pull' (e : expr typ func) : expr typ func :=
  match
    interleave (@setoid_rewrite typ func (expr typ func)
                                rel_dec
                                rewrite_exs)
               (fun rw e rvars rg rs =>
                  rw (beta_all (@apps _ _) nil nil e) rvars rg rs)
               10 e nil (RGinj (Inj (Eq tyProp)))
               (rsubst_empty _)
  with
    | None => e
    | Some (e,_) => e
  end.
*)

Time Eval vm_compute in quant_pull goal.
