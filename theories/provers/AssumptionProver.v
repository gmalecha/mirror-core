Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.List.
Require Import ExtLib.Tactics.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.Prover.
Require Import MirrorCore.provers.ProverTac.
Require Import MirrorCore.ExprProp.

Set Implicit Arguments.
Set Strict Implicit.

(** * The Assumption Prover **)

Section proverI.
  Context {typ : Type}.
  Context {RType_typ : RType typ}.
  Variable expr : Type.
  Context {Expr_expr : Expr _ expr}.
  Context {typ0_prop : Typ0 _ Prop}.
  Variable RD_expr : RelDec (@eq expr).
  Variable RDC_expr : RelDec_Correct RD_expr.
  Context {ExprOk_expr : ExprOk Expr_expr}.

  Definition assumption_summary : Type := list expr.

  Definition assumptionSummarize (hyps : list expr) : assumption_summary := hyps.

  Definition assumptionProve (hyps : assumption_summary)
             (_ _ : tenv typ)
             (goal : expr) : bool :=
    anyb (rel_dec goal) hyps.

  Definition assumptionLearn (sum : assumption_summary) (hyps : list expr)
  : assumption_summary :=
    hyps ++ sum.

  Definition assumptionValid (uvars vars : env) (sum : assumption_summary)
  : Prop :=
    AllProvable typ0_prop uvars vars sum.

  Lemma assumptionValid_extensible : forall u g f ue ge,
    assumptionValid u g f -> assumptionValid (u ++ ue) (g ++ ge) f.
  Proof.
    unfold assumptionValid. do 5 intro.
    eapply Forall_impl. intros.
    red in H. red.
    forward.
    eapply exprD_weaken in H; eauto.
    rewrite H. assumption.
  Qed.

  Lemma assumptionSummarizeCorrect : forall uvars vars hyps,
    AllProvable typ0_prop uvars vars hyps ->
    assumptionValid uvars vars (assumptionSummarize hyps).
  Proof. auto. Qed.

  Theorem Forall_app : forall T (P : T -> Prop) ls ls',
    Forall P (ls ++ ls') <->
    Forall P ls /\ Forall P ls'.
  Proof.
    induction ls; simpl; split; try inversion 1; intros; subst; auto.
    { apply IHls in H3. intuition. }
    { intuition. inversion H2; subst. constructor; auto.
      eapply IHls; intuition. }
  Qed.

  Lemma assumptionLearnCorrect : forall uvars vars sum,
    assumptionValid uvars vars sum -> forall hyps,
    AllProvable typ0_prop uvars vars hyps ->
    assumptionValid uvars vars (assumptionLearn sum hyps).
  Proof.
    unfold assumptionLearn, assumptionValid. intuition.
    apply Forall_app; auto.
  Qed.

  Theorem assumptionProveOk : ProveOk (Provable_val typ0_prop) assumptionValid assumptionProve.
  Proof.
    red. unfold assumptionValid, assumptionProve.
    induction sum; simpl; intros; try congruence.
    consider (goal ?[ eq ] a); intros; subst.
    { inversion H; subst; auto.
      red in H2. forward. }
    { inversion H; subst. eapply IHsum; eauto. }
  Qed.

  Definition assumptionProver : Prover typ expr :=
  {| Facts := assumption_summary
   ; Summarize := fun _ _ => assumptionSummarize
   ; Learn := fun f _ _ => assumptionLearn f
   ; Prove := assumptionProve
   |}.

  Definition assumptionProver_correct : ProverOk (Provable_val typ0_prop) assumptionProver.
  eapply Build_ProverOk with (Valid := assumptionValid);
    eauto using assumptionValid_extensible, assumptionSummarizeCorrect, assumptionLearnCorrect, assumptionProveOk.
  { simpl. intros. eapply assumptionLearnCorrect; eauto. }
  Qed.

End proverI.
