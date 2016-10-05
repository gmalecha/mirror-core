Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.

Require Import ExtLib.Core.RelDec.

Require Import McExamples.Tauto.MSimpleTyp.
Require Import McExamples.Tauto.ILogic.
Require Import McExamples.Tauto.ILogicFunc.
Require Import McExamples.Tauto.ILogicReify.

Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.MTypes.ModularTypes.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.PLemma.
Require Import MirrorCore.RTac.PApply.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.Polymorphic.
Require Import MirrorCore.Lambda.ExprUnify_simple.
Require Import MirrorCore.RTac.RTac.

Definition tc (t : typ) :=
  match t with
    | ModularTypes.tyProp => true
    | _ => false
  end.

Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.Reify.ReifyClass.

Definition test : (lemma typ (expr typ ilfunc) (expr typ ilfunc)) :=
  Eval unfold Lemma.add_var, Lemma.add_prem , Lemma.vars , Lemma.concl , Lemma.premises in
  <:: @limplAdj Prop _ _ ::>.

Print test.
Check limplAdj.

Definition conclD (us vs : tenv typ) (e : expr typ ilfunc) : option (exprT us vs Prop) :=
  exprD us vs tyProp e.

Definition r_refl : PolyLemma typ (expr typ ilfunc) (expr typ ilfunc) :=
  {| p_n := 1;
     p_lem := fun t => 
               {| vars := t :: nil;
                  premises := nil;
                  concl := App (App (Inj (fEntails t)) (Var 0)) (Var 0) |};
     p_tc := tc
  |}.

Lemma r_refl_sound : PolyLemmaD conclD r_refl.
Proof.
  unfold PolyLemmaD, with_typeclasses; simpl.
  destruct t; simpl in *; try apply I.
  unfold lemmaD; simpl; intros.
  intro H; apply H.
Qed.

Definition r_trueR : PolyLemma typ (expr typ ilfunc) (expr typ ilfunc) :=
  {| p_n := 1;
     p_lem := fun t => 
               {| vars := t :: nil;
                  premises := nil;
                  concl := App (App (Inj (fEntails t)) (Var 0)) (mkTrue t) |};
     p_tc := tc
  |}.

Lemma r_trueR_sound : PolyLemmaD conclD r_trueR.
Proof.
  unfold PolyLemmaD, with_typeclasses; simpl.
  destruct t; simpl in *; try apply I.
  unfold lemmaD; simpl; intros.
  unfold AbsAppI.exprT_App, exprT_Inj; simpl.
  unfold entailsR, castR; simpl; intros.
  apply I.
Qed.

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
               {| vars := t :: t :: t :: nil;
                  premises := App (App (Inj (fEntails t)) (Var 0)) (Var 2)
                                  :: App (App (Inj (fEntails t)) (Var 0)) (Var 1) :: nil;
                  concl := App (App (Inj (fEntails t)) (Var 0))
                               (App (App (Inj (fAnd t)) (Var 2)) (Var 1)) |};
     p_tc := tc
  |}.

Definition r_andL1 : PolyLemma typ (expr typ ilfunc) (expr typ ilfunc) :=
  {| p_n := 1;
     p_lem := fun t => 
               {| vars := t :: t :: t :: nil;
                  premises := App (App (Inj (fEntails t)) (Var 2))
                                  (Var 0) :: nil;
                  concl := App
                             (App (Inj (fEntails t))
                                  (App (App (Inj (fAnd t)) (Var 2))
                                       (Var 1))) (Var 0) |};
     p_tc := tc
  |}.

Definition r_andL2 : PolyLemma typ (expr typ ilfunc) (expr typ ilfunc) :=
  {| p_n := 1;
     p_lem := fun t => 
               {| vars := t :: t :: t :: nil;
                  premises := App (App (Inj (fEntails t)) (Var 1))
                                  (Var 0) :: nil;
                  concl := App
                             (App (Inj (fEntails t))
                                  (App (App (Inj (fAnd t)) (Var 2))
                                       (Var 1))) (Var 0) |};
     p_tc := tc
  |}.

Definition r_orL : PolyLemma typ (expr typ ilfunc) (expr typ ilfunc) :=
  {| p_n := 1;
     p_lem := fun t => 
               {| vars := t :: t :: t :: nil;
                  premises := App (App (Inj (fEntails t)) (Var 2))
                                  (Var 0)
                              :: App (App (Inj (fEntails t)) (Var 1))
                              (Var 0) :: nil;
                  concl := App
                             (App (Inj (fEntails t))
                                  (App (App (Inj (fOr t)) (Var 2)) (Var 1)))
                             (Var 0) |};
     p_tc := tc
  |}.

Definition r_orR1 : PolyLemma typ (expr typ ilfunc) (expr typ ilfunc) :=
  {| p_n := 1;
     p_lem := fun t => 
               {| vars := t :: t :: t :: nil;
                  premises := App (App (Inj (fEntails t)) (Var 0))
                                  (Var 2) :: nil;
                  concl := App (App (Inj (fEntails t)) (Var 0))
                               (App (App (Inj (fOr t)) (Var 2)) (Var 1)) |};
     p_tc := tc
  |}.

Definition r_orR2 : PolyLemma typ (expr typ ilfunc) (expr typ ilfunc) :=
  {| p_n := 1;
     p_lem := fun t => 
               {| vars := t :: t :: t :: nil;
                  premises := App (App (Inj (fEntails t)) (Var 0))
                                  (Var 1) :: nil;
                  concl := App (App (Inj (fEntails t)) (Var 0))
                               (App (App (Inj (fOr t)) (Var 2)) (Var 1)) |};
     p_tc := tc
  |}.

Definition r_implAdj : PolyLemma typ (expr typ ilfunc) (expr typ ilfunc) :=
  {| p_n := 1;
     p_lem := fun t => 
               {| vars := t :: t :: t :: nil;
                  premises := App
                                (App (Inj (fEntails t))
                                     (App (App (Inj (fAnd t)) (Var 0))
                                          (Var 2))) (Var 1) :: nil;
                  concl := App (App (Inj (fEntails t)) (Var 0))
                               (App (App (Inj (fImpl t)) (Var 2)) (Var 1)) |};
     p_tc := tc
  |}.


Definition PAPPLY (plem : PolyLemma typ (expr typ ilfunc) (expr typ ilfunc)) :=
  PAPPLY 
    (fun subst SS SU tus tvs n l r t s =>
              @exprUnify subst typ ilfunc RType_typ RSym_ilfunc Typ2_Fun
                         SS SU 10 tus tvs n l r t s) plem.

Definition fintro (e : expr typ ilfunc) : option (@OpenAs typ (expr typ ilfunc)) :=
  match e with
  | App (App (Inj (ilf_entails t1)) P) (App (Inj (ilf_exists t2 t3)) Q) =>
    if t1 ?[eq] t3 && tc t1 then
      Some (AsEx t2 (fun x => beta (App Q x)))
    else
      None
  | App (App (Inj (ilf_entails t1)) (App (Inj (ilf_forall t2 t3)) P)) Q =>
    if t1 ?[eq] t3 && tc t1 then
      Some (AsEx t2 (fun x => beta (App P x)))
    else
      None
  | App (App (Inj (ilf_entails t1)) (App (Inj (ilf_exists t2 t3)) P)) Q =>
    if t1 ?[eq] t3 && tc t1 then
      Some (AsAl t2 (fun x => beta (App P x)))
    else
      None
  | App (App (Inj (ilf_entails t1)) P) (App (Inj (ilf_forall t2 t3)) Q) =>
    if t1 ?[eq] t3 && tc t1 then
      Some (AsAl t2 (fun x => beta (App Q x)))
    else
      None
  | _ => None
  end.

Definition INTRO := @INTRO typ (expr typ ilfunc) ExprVar_expr ExprUVar_expr fintro.

Definition TAUTO : rtac typ (expr typ ilfunc) :=
  REC 10
      (fun r =>
         THEN (REPEAT 10 INTRO) 
              (runOnGoals 
                 (FIRST
                    (PAPPLY r_trueR ::
                     PAPPLY r_falseL :: 
                     PAPPLY r_refl :: 
                     THEN (PAPPLY r_andR) (runOnGoals r) :: 
                     THEN (PAPPLY r_orL) (runOnGoals r) :: 
                     SOLVE (THEN (PAPPLY r_orR1) (runOnGoals r)) :: 
                     SOLVE (THEN (PAPPLY r_orR2) (runOnGoals r)) :: 
                     SOLVE (THEN (PAPPLY r_andL1) (runOnGoals r)) :: 
                     SOLVE (THEN (PAPPLY r_andL2) (runOnGoals r)) :: nil)))) FAIL.

Goal True.
pose (PApply.get_lemma r_trueR
           (mkEntails tyProp (mkTrue tyProp) (mkTrue tyProp))).
compute in o.
(* Gregory, I'm pretty sure this should be evaluate to Some *)

apply I.
Qed.