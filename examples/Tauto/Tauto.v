Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.

Require Import ExtLib.Core.RelDec.

Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.MTypes.ModularTypes.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.PLemma.
Require Import MirrorCore.RTac.PApply.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.Polymorphic.
Require Import MirrorCore.Lambda.ExprUnify_simple.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Lambda.ExprTac.


Require Import McExamples.PolyRewrite.Monads.RtacDemo.
Require Import McExamples.Tauto.MSimpleTyp.
Require Import McExamples.Tauto.ILogic.
Require Import McExamples.Tauto.ILogicFunc.
Require Import McExamples.Tauto.ILogicReify.

Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.Reify.ReifyClass.

Definition ilogic_tc (gs : logic_ops) (t : typ) :=
  match gs t with
  | POption.pSome ILOps => @ILogic (typD t) ILOps
  | pNone => False
  end.

Definition test : (lemma typ (expr typ ilfunc) (expr typ ilfunc)) :=
  Eval unfold Lemma.add_var, Lemma.add_prem , Lemma.vars , Lemma.concl , Lemma.premises in
  <:: @limplAdj Prop _ _ ::>.


Section Tauto.

  Variable gs : logic_ops.
  Variable tc' : forall t, option (ilogic_tc gs t).

  Instance Expr_gs : Expr typ (expr typ ilfunc) := Expr_expr gs.

  Definition tc t :=
    match tc' t with
    | Some _ => true
    | _ => false
    end.

  Definition conclD (us vs : tenv typ) (e : expr typ ilfunc) : option (exprT us vs Prop) :=
    exprD_typ0 (T := Prop) us vs e.

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
    unfold PolyLemmaD, with_typeclasses; simpl; unfold tc; intros.
    remember (tc' t).
    destruct o; [clear Heqo|apply I].
    unfold ilogic_tc in i.
    remember (gs t).
    destruct p; [|intuition].
    unfold lemmaD, lemmaD', conclD, exprD_typ0; simpl; intros.
    repeat (red_exprD;
            (try rewrite <- Heqp);
            (try rewrite mtyp_cast_refl);
            unfold symAs; unfold AbsAppI.exprT_App; simpl; intros).
    reflexivity.
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
    unfold PolyLemmaD, with_typeclasses; simpl; unfold tc; intros.
    remember (tc' t).
    destruct o; [clear Heqo|apply I].
    unfold ilogic_tc in i.
    remember (gs t).
    destruct p; [|intuition].
    unfold lemmaD, lemmaD', conclD, exprD_typ0, mkTrue, fTrue; simpl; intros.
    repeat (red_exprD;
            (try rewrite <- Heqp);
            (try rewrite mtyp_cast_refl);
            unfold symAs; unfold AbsAppI.exprT_App; simpl; intros).
    apply ltrueR.
  Qed.

  Definition r_falseL : PolyLemma typ (expr typ ilfunc) (expr typ ilfunc) :=
    {| p_n := 1;
       p_lem := fun t =>
                  {| vars := t :: nil;
                     premises := nil;
                     concl := App (App (Inj (fEntails t)) (mkFalse t)) (Var 0) |};
       p_tc := tc
    |}.

  Lemma r_falseL_sound : PolyLemmaD conclD r_falseL.
  Proof.
    unfold PolyLemmaD, with_typeclasses; simpl; unfold tc; intros.
    remember (tc' t).
    destruct o; [clear Heqo|apply I].
    unfold ilogic_tc in i.
    remember (gs t).
    destruct p; [|intuition].
    unfold lemmaD, lemmaD', conclD, exprD_typ0, mkFalse, fFalse; simpl; intros.
    repeat (red_exprD;
            (try rewrite <- Heqp);
            (try rewrite mtyp_cast_refl);
            unfold symAs; unfold AbsAppI.exprT_App; simpl; intros).
    apply lfalseL.
  Qed.

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

  Lemma r_andR_sound : PolyLemmaD conclD r_andR.
  Proof.
    unfold PolyLemmaD, with_typeclasses; simpl; unfold tc; intros.
    remember (tc' t).
    destruct o; [clear Heqo|apply I].
    unfold ilogic_tc in i.
    remember (gs t).
    destruct p; [|intuition].
    unfold lemmaD, lemmaD', conclD, exprD_typ0, fAnd, fEntails; simpl; intros.
    repeat (red_exprD;
            (try rewrite <- Heqp);
            (try rewrite mtyp_cast_refl);
            unfold symAs; unfold AbsAppI.exprT_App; unfold exprD_typ0; simpl; intros).
    apply landR; assumption.
  Qed.

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

  Lemma r_andL1_sound : PolyLemmaD conclD r_andL1.
  Proof.
    unfold PolyLemmaD, with_typeclasses; simpl; unfold tc; intros.
    remember (tc' t).
    destruct o; [clear Heqo|apply I].
    unfold ilogic_tc in i.
    remember (gs t).
    destruct p; [|intuition].
    unfold lemmaD, lemmaD', conclD, exprD_typ0, fAnd, fEntails; simpl; intros.
    repeat (red_exprD;
            (try rewrite <- Heqp);
            (try rewrite mtyp_cast_refl);
            unfold symAs; unfold AbsAppI.exprT_App; unfold exprD_typ0; simpl; intros).
    apply landL1; assumption.
  Qed.

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

  Lemma r_andL2_sound : PolyLemmaD conclD r_andL2.
  Proof.
    unfold PolyLemmaD, with_typeclasses; simpl; unfold tc; intros.
    remember (tc' t).
    destruct o; [clear Heqo|apply I].
    unfold ilogic_tc in i.
    remember (gs t).
    destruct p; [|intuition].
    unfold lemmaD, lemmaD', conclD, exprD_typ0, fAnd, fEntails; simpl; intros.
    repeat (red_exprD;
            (try rewrite <- Heqp);
            (try rewrite mtyp_cast_refl);
            unfold symAs; unfold AbsAppI.exprT_App; unfold exprD_typ0; simpl; intros).
    apply landL2; assumption.
  Qed.


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

  Lemma r_orL_sound : PolyLemmaD conclD r_orL.
  Proof.
    unfold PolyLemmaD, with_typeclasses; simpl; unfold tc; intros.
    remember (tc' t).
    destruct o; [clear Heqo|apply I].
    unfold ilogic_tc in i.
    remember (gs t).
    destruct p; [|intuition].
    unfold lemmaD, lemmaD', conclD, exprD_typ0, fOr, fEntails; simpl; intros.
    repeat (red_exprD;
            (try rewrite <- Heqp);
            (try rewrite mtyp_cast_refl);
            unfold symAs; unfold AbsAppI.exprT_App; unfold exprD_typ0; simpl; intros).
    apply lorL; assumption.
  Qed.

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

  Lemma r_orR1_sound : PolyLemmaD conclD r_orR1.
  Proof.
    unfold PolyLemmaD, with_typeclasses; simpl; unfold tc; intros.
    remember (tc' t).
    destruct o; [clear Heqo|apply I].
    unfold ilogic_tc in i.
    remember (gs t).
    destruct p; [|intuition].
    unfold lemmaD, lemmaD', conclD, exprD_typ0, fAnd, fEntails; simpl; intros.
    repeat (red_exprD;
            (try rewrite <- Heqp);
            (try rewrite mtyp_cast_refl);
            unfold symAs; unfold AbsAppI.exprT_App; unfold exprD_typ0; simpl; intros).
    apply lorR1; assumption.
  Qed.

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

  Lemma r_orR2_sound : PolyLemmaD conclD r_orR2.
  Proof.
    unfold PolyLemmaD, with_typeclasses; simpl; unfold tc; intros.
    remember (tc' t).
    destruct o; [clear Heqo|apply I].
    unfold ilogic_tc in i.
    remember (gs t).
    destruct p; [|intuition].
    unfold lemmaD, lemmaD', conclD, exprD_typ0, fOr, fEntails; simpl; intros.
    repeat (red_exprD;
            (try rewrite <- Heqp);
            (try rewrite mtyp_cast_refl);
            unfold symAs; unfold AbsAppI.exprT_App; unfold exprD_typ0; simpl; intros).
    apply lorR2; assumption.
  Qed.

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

  Lemma r_implAdj_sound : PolyLemmaD conclD r_implAdj.
  Proof.
    unfold PolyLemmaD, with_typeclasses; simpl; unfold tc; intros.
    remember (tc' t).
    destruct o; [clear Heqo|apply I].
    unfold ilogic_tc in i.
    remember (gs t).
    destruct p; [|intuition].
    unfold lemmaD, lemmaD', conclD, exprD_typ0, fAnd, fImpl, fEntails; simpl; intros.
    repeat (red_exprD;
            (try rewrite <- Heqp);
            (try rewrite mtyp_cast_refl);
            unfold symAs; unfold AbsAppI.exprT_App; unfold exprD_typ0; simpl; intros).
    apply limplAdj; assumption.
  Qed.

  Definition PAPPLY (plem : PolyLemma typ (expr typ ilfunc) (expr typ ilfunc)) :=
    PAPPLY (RSym_func := RSym_ilfunc gs)
      (fun subst SS SU tus tvs n l r t s =>
         @exprUnify subst typ ilfunc RType_typ (RSym_ilfunc gs) Typ2_Fun
                    SS SU 10 tus tvs n l r t s) ilfunc_unify plem.

  Definition fintro (e : expr typ ilfunc) : option (@OpenAs typ (expr typ ilfunc)) :=
    match e with
    | App (App (Inj (ilf_entails t1)) P) (App (Inj (ilf_exists t2 t3)) Q) =>
      if t1 ?[eq] t3 && tc t1 then
        Some (AsEx t2 (fun x => mkEntails t1 P (beta (App Q x))))
      else
        None
    | App (App (Inj (ilf_entails t1)) (App (Inj (ilf_forall t2 t3)) P)) Q =>
      if t1 ?[eq] t3 && tc t1 then
        Some (AsEx t2 (fun x => mkEntails t1 (beta (App P x)) Q))
      else
        None
    | App (App (Inj (ilf_entails t1)) (App (Inj (ilf_exists t2 t3)) P)) Q =>
      if t1 ?[eq] t3 && tc t1 then
        Some (AsAl t2 (fun x => mkEntails t1 (beta (App P x)) Q))
      else
        None
    | App (App (Inj (ilf_entails t1)) P) (App (Inj (ilf_forall t2 t3)) Q) =>
      if t1 ?[eq] t3 && tc t1 then
        Some (AsAl t2 (fun x => mkEntails t1 P (beta (App Q x))))
      else
        None
    | _ => None
    end.

  Lemma fintro_sound : open_sound fintro.
  Proof.
    admit.
    (*
    unfold open_sound, fintro; intros.
    destruct e; simpl in H; try inversion H; clear H1.
    destruct e1; simpl in H; try inversion H; clear H1.
    destruct e1_1; simpl in H; try inversion H; clear H1.
    destruct i; simpl in H; try inversion H; clear H1.
    destruct e1_2; simpl in H; try inversion H; clear H1.
    destruct e2; simpl in H; try inversion H; clear H1.
    destruct e2_1; simpl in H; try inversion H; clear H1.
    destruct i; simpl in H; try inversion H; clear H1.
    remember (logic ?[eq] logic0 && tc logic).
    destruct b; [symmetry in Heqb|inversion H].
    rewrite andb_true_iff in Heqb; destruct Heqb as [Hl Htc].
    rewrite rel_dec_correct in Hl; subst.
    inversion H; subst; clear H.
    unfold tc in Htc.
    destruct (tc' logic0); [clear Htc|inversion Htc].
    unfold ilogic_tc in i.
    destruct (gs logic0); [|destruct i].
Print open_spec.
    unfold open_spec; intros; simpl in *.

    reduce_exprT.
    unfold propD, exprD_typ0 in H.
    unfold exprD in H; simpl in H.
    reduce_exprT.
Print Ltac reduce_exprT.
prove_lem idtac.
unfold ExprDsimul.ExprDenote.lambda_exprD in H.
    *)
  Admitted.

  Definition INTRO := @INTRO typ (expr typ ilfunc) ExprVar_expr ExprUVar_expr fintro.

  Definition TAUTO n : rtac typ (expr typ ilfunc) :=
    REC n
        (fun r => THEN INSTANTIATE (runOnGoals (
           THEN (REPEAT n INTRO)
                (runOnGoals
                   (FIRST
                      (PAPPLY r_trueR ::
                       PAPPLY r_falseL ::
                       PAPPLY r_refl ::
                       THEN (PAPPLY r_andR) (runOnGoals r) ::
                       THEN (PAPPLY r_implAdj) (runOnGoals r) ::
                       THEN (PAPPLY r_orL) (runOnGoals r) ::
                       SOLVE (THEN (PAPPLY r_orR1) (runOnGoals r)) ::
                       SOLVE (THEN (PAPPLY r_orR2) (runOnGoals r)) ::
                       SOLVE (THEN (PAPPLY r_andL1) (runOnGoals r)) ::
                       SOLVE (THEN (PAPPLY r_andL2) (runOnGoals r)) :: nil)))))) IDTAC.

  Lemma TAUTO_sound : forall n, rtac_sound (TAUTO n).
  Proof.
    unfold TAUTO.
    rtac_derive_soundness_default.
    apply INSTANTIATE_sound.
    apply INTRO_sound.
    apply fintro_sound.
    apply PAPPLY_sound; [intros; apply exprUnify_sound; apply _ |
                         split; apply r_trueR_sound].
    apply PAPPLY_sound; [intros; apply exprUnify_sound; apply _ |
                         split; apply r_falseL_sound].
    apply PAPPLY_sound; [intros; apply exprUnify_sound; apply _ |
                         split; apply r_refl_sound].
    apply PAPPLY_sound; [intros; apply exprUnify_sound; apply _ |
                         split; apply r_andR_sound].
    apply PAPPLY_sound; [intros; apply exprUnify_sound; apply _ |
                         split; apply r_implAdj_sound].
    apply PAPPLY_sound; [intros; apply exprUnify_sound; apply _ |
                         split; apply r_orL_sound].
    apply PAPPLY_sound; [intros; apply exprUnify_sound; apply _ |
                         split; apply r_orR1_sound].
    apply PAPPLY_sound; [intros; apply exprUnify_sound; apply _ |
                         split; apply r_orR2_sound].
    apply PAPPLY_sound; [intros; apply exprUnify_sound; apply _ |
                         split; apply r_andL1_sound].
    apply PAPPLY_sound; [intros; apply exprUnify_sound; apply _ |
                         split; apply r_andL2_sound].
  Qed.


End Tauto.

Definition gs : logic_ops :=
  fun t =>
    match t with
    | ModularTypes.tyProp => POption.pSome ILogicOps_Prop
    | _ => POption.pNone
    end.

Definition gs' t : option (ilogic_tc gs t) :=
  match t with
    | ModularTypes.tyProp => Some ILogic_Prop
    | _ => None
  end.

Fixpoint mkAnds n :=
  match n with
  | 0 => Var 0
  | S n => mkAnd tyProp (Var (S n)) (mkAnds n)
  end.

Fixpoint mkImpls n P :=
  match n with
  | 0 => mkImpl tyProp (Var 0) P
  | S n => mkImpl tyProp (Var (S n)) (mkImpls n P)
  end.

Fixpoint mkForalls n P :=
  match n with
  | 0 => mkForall tyProp tyProp P
  | S n => mkForall tyProp tyProp (mkForalls n P)
  end.

Definition mkTerm n := mkForalls n (mkImpls n (mkAnds n)).

Fixpoint mkBigTerm n m :=
  match n with
  | 0 => mkTerm m
  | S n => mkAnd tyProp (mkTerm m) (mkBigTerm n m)
  end.


Goal True.
pose (TAUTO gs gs' 10 (CTop nil nil) (TopSubst (expr typ ilfunc) nil nil)
       (mkEntails tyProp (mkTrue tyProp)
          (mkAnd tyProp
             (mkForall tyProp tyProp (mkImpl tyProp (Var 0) (Var 0)))
             (mkForall tyProp tyProp (mkImpl tyProp (Var 0) (Var 0)))))).
compute in r.

  pose (TAUTO gs gs' 10 (CTop nil nil) (TopSubst _ nil nil)
              (mkEntails tyProp (mkTrue tyProp) (mkBigTerm 1 0))).
  unfold mkBigTerm, mkTerm, mkForalls, mkImpls, mkAnds in r.
  Time vm_compute in r0.
  (* I do not think that this should fail *)

  apply I.
Qed.