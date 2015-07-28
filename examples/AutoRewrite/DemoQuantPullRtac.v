Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprD.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.AutoSetoidRewriteRtac.
Require Import McExamples.Simple.Simple.

Set Implicit Arguments.
Set Strict Implicit.

Definition fAnd a b : expr typ func := App (App (Inj Simple.And) a) b.
Definition fOr a b : expr typ func := App (App (Inj Simple.And) a) b.
Definition fAll t P : expr typ func := App (Inj (Simple.All t)) (Abs t P).
Definition fEx t P : expr typ func := App (Inj (Simple.Ex t)) (Abs t P).
Definition fEq t : expr typ func := (Inj (Simple.Eq t)).
Definition fEq_nat a b : expr typ func := App (App (fEq tyNat) a) b.
Definition fN n : expr typ func := Inj (Simple.N n).

Let Rbase := expr typ func.

Definition m : Type -> Type :=
  @mrw typ func.

Fixpoint goal n : expr typ func :=
  match n with
  | 0 => fEq_nat (fN 0) (fN 0)
  | S n =>
    fAnd (fEx tyNat (goal n)) (fEx tyNat (goal n))
  end.

Theorem pull_ex_nat_and_left
: forall T P Q, ((exists n : T, P n) /\ Q) = (exists n, P n /\ Q).
Admitted.

Definition lem_pull_ex_nat_and_left : rw_lemma (typ:=typ) (func:=func) (expr typ func) :=
{| Lemma.vars := tyArr tyNat tyProp :: tyProp :: nil
 ; Lemma.premises := nil
 ; Lemma.concl := {| lhs := fAnd (App (Inj (Simple.Ex tyNat)) (Var 0)) (Var 1)
             ; rel := Rinj (fEq tyProp)
             ; rhs := fEx tyNat (fAnd (App (Var 1) (Var 0)) (Var 2))
             |}
 |}.

Existing Instance RType_typ.
Existing Instance Expr.Expr_expr.

Definition RbaseD (e : expr typ func) (t : typ)
: option (TypesI.typD t -> TypesI.typD t -> Prop) :=
  exprD nil nil e (tyArr t (tyArr t tyProp)).

Eval compute in Lemma.lemmaD (@rw_conclD _ _ _ _ _ _ RbaseD)
                             nil nil lem_pull_ex_nat_and_left .

Theorem pull_ex_nat_and_right
: forall T P Q, (Q /\ (exists n : T, P n)) = (exists n, Q /\ P n).
Admitted.

Definition lem_pull_ex_nat_and_right : rw_lemma (typ:=typ) (func:=func) (expr typ func) :=
{| Lemma.vars := tyArr tyNat tyProp :: tyProp :: nil
 ; Lemma.premises := nil
 ; Lemma.concl := {| lhs := fAnd (Var 1) (App (Inj (Simple.Ex tyNat)) (Var 0))
             ; rel := Rinj (fEq tyProp)
             ; rhs := fEx tyNat (fAnd (Var 2) (App (Var 1) (Var 0)))
             |}
 |}.

Fixpoint is_refl (r : @R typ (expr typ func)) : bool :=
  match r with
  | Rinj (Inj (Eq _)) => true
  | Rinj (Inj Impl) => true
  | Rpointwise _ x => is_refl x
  | Rrespects (Rinj (Inj (Eq _))) x => is_refl x
  | _ => false
  end.

Fixpoint is_trans (r : @R typ (expr typ func)) : bool :=
  match r with
  | Rinj (Inj (Eq _)) => true
  | Rinj (Inj Lt) => true
  | Rinj (Inj Impl) => true
  | Rpointwise _ x => is_trans x
  | Rrespects (Rinj (Inj (Eq _))) x => is_trans x
  | _ => false
  end.

Definition get_respectful :=
  do_respectful (expr_eq_sdec (typ:=typ) (func:=func) _ rel_dec)
    ((Inj (Ex tyNat), Rrespects (Rpointwise tyNat (Rinj (Inj Impl))) (Rinj (Inj Impl))) ::
     (Inj (All tyNat), Rrespects (Rpointwise tyNat (Rinj (Inj Impl))) (Rinj (Inj Impl))) ::
     (Inj And, Rrespects (Rinj (Inj Impl)) (Rrespects (Rinj (Inj Impl)) (Rinj (Inj Impl)))) ::
     (Inj Or, Rrespects (Rinj (Inj Impl)) (Rrespects (Rinj (Inj Impl)) (Rinj (Inj Impl)))) ::
     (Inj Plus, Rrespects (Rinj (Inj (Eq tyNat))) (Rrespects (Rinj (Inj (Eq tyNat))) (Rinj (Inj (Eq tyNat))))) ::

nil).

Definition the_rewrites
           (lems : list (rw_lemma (typ:=typ) (func:=func) (expr typ func) * CoreK.rtacK typ (expr typ func)))
: expr typ func -> R (typ:=typ) Rbase -> mrw (typ:=typ) (func:=func) (expr typ func) :=
  @using_rewrite_db typ func _ _ _ _ (expr typ func) (@expr_eq_sdec typ func _ rel_dec) lems.

Require Import MirrorCore.RTac.RunOnGoals.
Require Import MirrorCore.RTac.Idtac.

Definition the_lemmas : list (rw_lemma (typ:=typ) (func:=func) (expr typ func) * CoreK.rtacK typ (expr typ func)) :=
  (lem_pull_ex_nat_and_left, ON_ALL IDTAC) ::
  (lem_pull_ex_nat_and_right, ON_ALL IDTAC) ::
  nil.

(** this doesn't lift everything, but it does what it is programmed to do **)
Definition quant_pull (e : expr typ func) : mrw (expr typ func) :=
  bottom_up is_refl is_trans (the_rewrites the_lemmas) get_respectful
            e (Rinj (Inj (Eq tyProp))).

Time Eval vm_compute
  in match quant_pull (goal 19) nil nil nil 0 0 (TopSubst _ nil nil) with
     | None => tt
     | Some _ => tt
     end.


(*
  match
(*    rw_fix 10 (@setoid_rewrite typ func (expr typ func)
                     rel_dec
                     rewrite_exs rewrite_respects)
      e nil (RGinj (Inj (Eq tyProp)))
      (rsubst_empty _)
*)
  with
    | None => e
    | Some (e,_) => e
  end.
*)

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


(*
Definition rewrite_exs (e : expr typ func) (rvars : list (R (expr typ func)))
           (rg : R (expr typ func)) : m (expr typ func) :=
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

*)
