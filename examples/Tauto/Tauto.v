Require Import Coq.Lists.List.
Require Import MirrorCore.MTypes.ModularTypes.
Require Import MirrorCore.Lambda.ExprCore.
Require Import McExamples.Tauto.MSimpleTyp.
Require Import McExamples.Tauto.ILogic.
Require Import McExamples.Tauto.ILogicFunc.
Require Import McExamples.Tauto.ILogicReify.

Require Import MirrorCore.PLemma.
Require Import MirrorCore.RTac.PApply.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.Polymorphic.
Require Import MirrorCore.Lambda.ExprUnify_simple.
Require Import MirrorCore.RTac.RTac.

Definition tc (t : typ) :=
  match t with
    | ModularTypes.tyProp => true
    | _ => true
  end.

Definition r_trueR : PolyLemma typ (expr typ ilfunc) (expr typ ilfunc) :=
  {| p_n := 1;
     p_lem := fun t => 
               {| vars := t :: nil;
                  premises := nil;
                  concl := App (App (Inj (fEntails t)) (Var 0)) (mkTrue t) |};
     p_tc := tc
  |}.

Definition r_falseL : PolyLemma typ (expr typ ilfunc) (expr typ ilfunc) :=
  {| p_n := 1;
     p_lem := fun t => 
               {| vars := t :: nil;
                  premises := nil;
                  concl := App (App (Inj (fEntails t)) (mkFalse t)) (Var 0) |};
     p_tc := tc
  |}.

Definition r_andR : PolyLemma typ (expr typ ilfunc) (expr typ ilfunc) :=
  {| p_n := 1;
     p_lem := fun t => 
               {| vars := t :: nil;
                  premises := App (App (Inj (fEntails t)) (Var 0)) (Var 2)
                                  :: App (App (Inj (fEntails t)) (Var 0)) (Var 1) :: nil;
                  concl := App (App (Inj (fEntails t)) (Var 0))
                               (App (App (Inj (fAnd t)) (Var 2)) (Var 1)) |};
     p_tc := tc
  |}.

Definition PAPPLY (plem : PolyLemma typ (expr typ ilfunc) (expr typ ilfunc)) :=
  PAPPLY 
    (fun subst SS SU tus tvs n l r t s =>
              @exprUnify subst typ ilfunc RType_typ RSym_ilfunc Typ2_Fun
                         SS SU 10 tus tvs n l r t s) plem.


Definition TAUTO : rtac typ (expr typ ilfunc) :=
  REC 10
      (fun r =>
         (FIRST
            (PAPPLY r_trueR ::
             PAPPLY r_falseL :: 
             THEN (PAPPLY r_andR) (runOnGoals r) :: nil))) FAIL.

Goal True.
pose (PApply.get_lemma r_trueR
           (mkEntails tyProp (mkTrue tyProp) (mkTrue tyProp))).
compute in o.
(* Gregory, I'm pretty sure this should be evaluate to Some *)

apply I.
Qed.