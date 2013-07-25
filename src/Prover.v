Require Import List Arith Bool.
Require Import ExtLib.Structures.EqDep.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Data.HList.
Require Import ExprCore ExprProp ExprT Repr.

Set Implicit Arguments.
Set Strict Implicit.

(** Provers that establish [expr]-encoded facts *)

Definition ProverCorrect types (fs : functions types) (summary : Type)
  (** Some prover work only needs to be done once per set of hypotheses,
      so we do it once and save the outcome in a summary of this type. *)
  (valid : env types -> env types -> summary -> Prop)
  (prover : summary -> expr types -> bool) : Prop :=
  forall vars uvars sum,
    valid uvars vars sum ->
    forall goal, 
      prover sum goal = true ->
      WellTyped_expr (typeof_funcs fs) (typeof_env uvars) (typeof_env vars) goal tvProp ->
      Provable fs uvars vars goal.

Record ProverT (types : list type) : Type :=
{ Facts : Type
; Summarize : exprs types -> Facts
; Learn : Facts -> exprs types -> Facts
; Prove : Facts -> expr types -> bool
}.

Record ProverT_correct (types : list type) (P : ProverT types) (funcs : functions types) : Type :=
{ Valid : env types -> env types -> Facts P -> Prop
; Valid_weaken : forall u g f ue ge,
  Valid u g f -> Valid (u ++ ue) (g ++ ge) f
; Summarize_correct : forall uvars vars hyps, 
  AllProvable funcs uvars vars hyps ->
  Valid uvars vars (Summarize P hyps)
; Learn_correct : forall uvars vars facts,
  Valid uvars vars facts -> forall hyps,
  AllProvable funcs uvars vars hyps ->
  Valid uvars vars (Learn P facts hyps)
; Prove_correct : ProverCorrect funcs Valid (Prove P)
}.

Record ProverPackage : Type :=
{ ProverTypes : Repr type
; ProverFuncs : forall ts, Repr (function (repr ProverTypes ts))
; Prover : forall ts, ProverT (repr ProverTypes ts)
; Prover_correct : forall ts fs, 
  ProverT_correct (Prover ts) (repr (ProverFuncs ts) fs)
}.


(** Generic lemmas/tactis to prove things about provers **)

Hint Rewrite equiv_dec_refl_left (*SemiDec_EquivDec_refl_left*) : provers.

(** Composite Prover **)
Section composite.
  Variable types : list type.
  Variables pl pr : ProverT types.

  Definition composite_ProverT : ProverT types :=
  {| Facts := Facts pl * Facts pr
   ; Summarize := fun hyps =>
     (Summarize pl hyps, Summarize pr hyps)
   ; Learn := fun facts hyps =>
     let (fl,fr) := facts in
     (Learn pl fl hyps, Learn pr fr hyps)
   ; Prove := fun facts goal =>
     let (fl,fr) := facts in
     (Prove pl fl goal) || (Prove pr fr goal)
   |}.

  Variable funcs : functions types.
  Variable pl_correct : ProverT_correct pl funcs.
  Variable pr_correct : ProverT_correct pr funcs.

  Theorem composite_ProverT_correct : ProverT_correct composite_ProverT funcs.
    
    refine (
      {| Valid := fun uvars vars (facts : Facts composite_ProverT) =>
        let (fl,fr) := facts in
          Valid pl_correct uvars vars fl /\ Valid pr_correct uvars vars fr
      |}); destruct pl_correct; destruct pr_correct; simpl; try destruct facts; intuition eauto.
    unfold ProverCorrect. destruct sum; intuition.
    apply orb_true_iff in H.
    destruct H; eauto.
  Qed.
End composite.