Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.ProverI.
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

  Definition assumptionValid (tus tvs : list typ) (sum : assumption_summary)
  : ResType tus tvs Prop :=
    AllProvable tus tvs sum.

  Lemma assumptionValid_extensible
  : forall u g f gD,
      assumptionValid u g f = Some gD ->
      forall ue ge,
      exists gD',
        assumptionValid (u ++ ue) (g ++ ge) f = Some gD'
        /\ forall us vs us' vs',
             gD us vs <-> gD' (HList.hlist_app us us') (HList.hlist_app vs vs').
  Proof.
    intros.
    eapply AllProvable_weaken with (tus' := ue) (tvs' := ge) in H; eauto.
    forward_reason.
    eexists; split; eauto.
  Qed.

  Lemma assumptionSummarizeCorrect : forall uvars vars hyps premD,
    AllProvable uvars vars hyps = Some premD ->
    exists premD',
      assumptionValid uvars vars (assumptionSummarize hyps) = Some premD'
      /\ forall us vs, premD us vs -> premD' us vs.
  Proof.
    unfold assumptionValid, assumptionSummarize. eauto.
  Qed.

  (** TODO: Move **)
(*
  Theorem Forall_app : forall T (P : T -> Prop) ls ls',
    Forall P (ls ++ ls') <->
    Forall P ls /\ Forall P ls'.
  Proof.
    induction ls; simpl; split; try inversion 1; intros; subst; auto.
    { apply IHls in H3. intuition. }
    { intuition. inversion H2; subst. constructor; auto.
      eapply IHls; intuition. }
  Qed.
*)

  Lemma assumptionLearnCorrect : forall uvars vars sum sD,
    assumptionValid uvars vars sum = Some sD ->
    forall hyps hD,
      AllProvable uvars vars hyps = Some hD ->
      exists sD',
        assumptionValid uvars vars (assumptionLearn sum hyps) = Some sD' /\
        forall us vs,
          hD us vs -> sD us vs -> sD' us vs.
  Proof.
    unfold assumptionLearn, assumptionValid. intuition.
    eapply AllProvable_app in H; eauto.
    forward_reason.
    eexists; split; eauto.
    intros. eapply H1. intuition.
  Qed.

  Theorem assumptionProveOk
  : ProveOk assumptionValid assumptionProve.
  Proof.
    red. unfold assumptionValid, assumptionProve.
    induction sum; simpl; intros; try congruence.
    consider (goal ?[ eq ] a); intros; subst.
    { eapply AllProvable_cons in H0.
      forward_reason.
      rewrite H1 in *. inv_all; subst.
      eapply H3 in H2. intuition. }
    { eapply AllProvable_cons in H0.
      forward_reason.
      specialize (IHsum _ H3 _ _ H4 H1).
      eapply H5 in H2.
      eapply IHsum. intuition. }
  Qed.

  Definition assumptionProver : @Prover typ expr :=
  {| Facts := assumption_summary
   ; Summarize := fun _ _ => assumptionSummarize
   ; Learn := fun f _ _ => assumptionLearn f
   ; Prove := assumptionProve
   |}.

  Definition assumptionProver_correct : ProverOk assumptionProver.
  eapply Build_ProverOk with (factsD := assumptionValid);
    eauto using assumptionValid_extensible, assumptionSummarizeCorrect, assumptionLearnCorrect, assumptionProveOk.
  { simpl. intros. eapply assumptionLearnCorrect; eauto. }
  Qed.

End proverI.
