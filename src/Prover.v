Require Import List Arith Bool.
Require Import ExtLib.Structures.EqDep.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Data.HList.
Require Import MirrorCore.Iso.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprProp.

Set Implicit Arguments.
Set Strict Implicit.

(** Provers that establish [expr]-encoded facts *)
Section proverI.
  Context {typ : Type}.
  Variable typD : list Type -> typ -> Type.
  Context {RType_typ : RType typD}.
  Variable expr : Type.
  Context {Expr_expr : Expr typD expr}.
  Context {typ0_prop : TypInstance0 typD Prop}.

  (** TODO: It may be adventageous to have a non-prop prover,
   **       to allow asking to prove equality facts.
   **)

  Record ProverT : Type :=
  { Facts : Type
  ; Summarize : tenv typ -> tenv typ -> list expr -> Facts
  ; Learn : Facts -> tenv typ -> tenv typ -> list expr -> Facts
  ; Prove : Facts -> tenv typ -> tenv typ -> expr -> bool
  }.

  Definition ProverCorrect (summary : Type)
    (** Some prover work only needs to be done once per set of hypotheses,
        so we do it once and save the outcome in a summary of this type. *)
    (valid : env typD -> env typD -> summary -> Prop)
    (prover : summary -> tenv typ -> tenv typ -> expr -> bool) : Prop :=
    forall vars uvars sum,
      valid uvars vars sum ->
      forall goal,
        prover sum (typeof_env uvars) (typeof_env vars) goal = true ->
        match exprD uvars vars goal (@typ0 _ _ _ typ0_prop) return Prop with
          | None => True
          | Some P => soutof (iso := @typ0_iso _ _ _ typ0_prop nil) (fun x => x) P
        end.
(*
        WellTyped_expr (typeof_env uvars) (typeof_env vars) goal tvProp ->
        Provable uvars vars goal.
*)

  Record ProverT_correct (P : ProverT) : Type :=
  { Valid : env typD -> env typD -> Facts P -> Prop
  ; Valid_weaken : forall u g f ue ge,
    Valid u g f -> Valid (u ++ ue) (g ++ ge) f
  ; Summarize_correct : forall (uvars vars : env typD) (hyps : list expr),
    Forall (Provable (expr := expr) typ0_prop uvars vars) hyps ->
    Valid uvars vars (Summarize P (typeof_env uvars) (typeof_env vars) hyps)
  ; Learn_correct : forall uvars vars facts,
    Valid uvars vars facts -> forall hyps,
    Forall (Provable typ0_prop uvars vars) hyps ->
    Valid uvars vars (P.(Learn) facts (typeof_env uvars) (typeof_env vars) hyps)
  ; Prove_correct : ProverCorrect Valid P.(Prove)
  }.


  (** Composite Prover **)
  Section composite.
    Variables pl pr : ProverT.

    Definition composite_ProverT : ProverT :=
    {| Facts := Facts pl * Facts pr
     ; Summarize := fun uenv venv hyps =>
         (pl.(Summarize) uenv venv hyps, pr.(Summarize) uenv venv hyps)
     ; Learn := fun facts uenv venv hyps =>
         let (fl,fr) := facts in
         (pl.(Learn) fl uenv venv hyps, pr.(Learn) fr uenv venv hyps)
     ; Prove := fun facts uenv venv goal =>
         let (fl,fr) := facts in
         if pl.(Prove) fl uenv venv goal then true
         else pr.(Prove) fr uenv venv goal
    |}.

    Variable pl_correct : ProverT_correct pl.
    Variable pr_correct : ProverT_correct pr.

    Theorem composite_ProverT_correct : ProverT_correct composite_ProverT.
    Proof.
      refine (
        {| Valid := fun uvars vars (facts : Facts composite_ProverT) =>
             let (fl,fr) := facts in
             Valid pl_correct uvars vars fl /\ Valid pr_correct uvars vars fr
         |});
      (destruct pl_correct; destruct pr_correct; simpl;
       try destruct facts; intuition eauto).
      unfold ProverCorrect. destruct sum; intuition.
      consider (Prove pl f (typeof_env uvars) (typeof_env vars) goal); intros.
      eapply Prove_correct0; eassumption.
      eapply Prove_correct1; eassumption.
    Qed.
  End composite.
End proverI.