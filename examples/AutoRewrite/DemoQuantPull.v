Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprD.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.AutoSetoidRewriteRtac.
Require Import MirrorCore.Reify.Reify.
Require Import McExamples.Simple.Simple.
Require Import McExamples.Simple.SimpleReify.

Set Implicit Arguments.
Set Strict Implicit.

Definition fAnd a b : expr typ func := App (App (Inj Simple.And) a) b.
Definition fOr a b : expr typ func := App (App (Inj Simple.And) a) b.
Definition fAll t P : expr typ func := App (Inj (Simple.All t)) (Abs t P).
Definition fEx t P : expr typ func := App (Inj (Simple.Ex t)) (Abs t P).
Definition fEq_nat a b : expr typ func := App (App (Inj (Simple.Eq tyNat)) a) b.
Definition fN n : expr typ func := Inj (Simple.N n).

Let Rbase := expr typ func.

Reify Declare Patterns patterns_concl := (rw_concl typ func Rbase).

Reify Declare Syntax reify_concl_base :=
  (@CPatterns _ patterns_concl).

Local Notation "x @ y" := (@RApp x y) (only parsing, at level 30).
Local Notation "'!!' x" := (@RExact _ x) (only parsing, at level 25).
Local Notation "'?' n" := (@RGet n RIgnore) (only parsing, at level 25).
Local Notation "'?!' n" := (@RGet n RConst) (only parsing, at level 25).
Local Notation "'#'" := RIgnore (only parsing, at level 0).

Reify Pattern patterns_concl += (?0 @ ?1 @ ?2) =>
  (fun (a b c : function reify_simple) =>
     @Build_rw_concl typ func Rbase b (@Rinj typ Rbase a) c).

Definition goal : expr typ func :=
  fAnd (fEx tyNat (fEq_nat (Var 0) (fN 3)))
       (fEx tyNat (fEq_nat (Var 0) (fN 7))).

Axiom pull_ex_and_left (T: Type)
: forall (P : T -> Prop) (Q : Prop), ((exists n : T, P n) /\ Q) = (exists n, P n /\ Q).

Reify BuildLemma < reify_simple_typ reify_simple reify_concl_base >
      lem_pull_ex_nat_and_left : @pull_ex_and_left nat.

Axiom pull_ex_and_right (T : Type)
: forall P Q, (Q /\ (exists n : T, P n)) = (exists n, Q /\ P n).

Reify BuildLemma < reify_simple_typ reify_simple reify_concl_base >
      lem_pull_ex_nat_and_right : @pull_ex_and_right nat.

Require Import MirrorCore.RTac.IdtacK.

Definition rewrite_exs : lem_rewriter typ func Rbase :=
  using_rewrite_db rel_dec ((lem_pull_ex_nat_and_left, IDTACK) ::
                            (lem_pull_ex_nat_and_right, IDTACK) :: nil).

Local Notation "a [==>] b" := (@Rrespects _ _ a b) (at level 30, right associativity).
Local Notation "a [..>] b" := (@Rpointwise _ _ a b) (at level 30, right associativity).

Definition respects_exs : respectful_dec typ func Rbase :=
  do_respectful rel_dec
                ((Inj Simple.And,
                  Rinj (Inj (Eq tyProp)) [==>] Rinj (Inj (Eq tyProp)) [==>] Rinj (Inj (Eq tyProp))) ::
                 (Inj (Simple.Ex tyNat), (tyNat [..>] Rinj (Inj (Eq tyProp))) [==>] Rinj (Inj (Eq tyProp)))
                 :: nil).

(*
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


Time Eval vm_compute in quant_pull goal.
*)