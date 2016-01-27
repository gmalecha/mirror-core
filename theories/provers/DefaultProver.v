(** The default prover doesn't solve anything! **)
Require Import ExtLib.Tactics.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.ProverI.

Set Implicit Arguments.
Set Strict Implicit.

Section default_prover.
  Context {typ : Type}.
  Context {RType_typ : RType typ}.
  Variable expr : Type.
  Context {Expr_expr : Expr _ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.

  Definition DefaultProver : @Prover typ expr :=
  {| Facts := unit
   ; Summarize := fun tus tvs es => tt
   ; Learn := fun t _ _ _ => t
   ; Prove := fun _ _ _ _ => false
   |}.

  Theorem DefaultProverOk : ProverOk DefaultProver.
  Proof.
  refine
    {| factsD := fun _ _ _ => Some (fun _ _ => True) |}.
  { intros. inv_all; subst. eexists; split; eauto.
    simpl. intuition. }
  { intros. inv_all; subst. eexists; split; eauto.
    simpl. intuition. }
  { intros. inv_all; subst. eexists; split; eauto. }
  { red. simpl. inversion 2. }
  Qed.
End default_prover.