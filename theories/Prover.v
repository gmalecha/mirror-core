Require Import Coq.Lists.List Coq.Bool.Bool.
Require Import ExtLib.Tactics.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.EnvI.

Set Implicit Arguments.
Set Strict Implicit.

(** Provers that establish [expr]-encoded facts *)
Section proverI.
  Variable typ : Type.
  Variable typD : list Type -> typ -> Type.
  Context {RType_typ : RType typD}.
  Variable expr : Type.
  Context {Expr_expr : Expr typD expr}.
  Context {ty : typ}.
  Variable Provable' : typD nil ty -> Prop.

  Let Provable (us vs : env typD) (e : expr) : Prop :=
    match exprD us vs e ty with
      | None => False
      | Some val => Provable' val
    end.


  Record Prover : Type :=
  { Facts : Type
  ; Summarize : tenv typ -> tenv typ -> list expr -> Facts
  ; Learn : Facts -> tenv typ -> tenv typ -> list expr -> Facts
  ; Prove : Facts -> tenv typ -> tenv typ -> expr -> bool
  }.

  Definition ProveOk (summary : Type)
    (** Some prover work only needs to be done once per set of hypotheses,
        so we do it once and save the outcome in a summary of this type. *)
    (valid : env typD -> env typD -> summary -> Prop)
    (prover : summary -> tenv typ -> tenv typ -> expr -> bool) : Prop :=
    forall vars uvars sum,
      valid uvars vars sum ->
      forall goal,
        prover sum (typeof_env uvars) (typeof_env vars) goal = true ->
        match exprD uvars vars goal ty with
          | None => True
          | Some val => Provable' val
        end.

  Record ProverOk (P : Prover) : Type :=
  { Valid : env typD -> env typD -> Facts P -> Prop
  ; Valid_weaken : forall u g f ue ge,
    Valid u g f -> Valid (u ++ ue) (g ++ ge) f
  ; Summarize_correct : forall (uvars vars : env typD) (hyps : list expr),
    Forall (Provable uvars vars) hyps ->
    Valid uvars vars (Summarize P (typeof_env uvars) (typeof_env vars) hyps)
  ; Learn_correct : forall uvars vars facts,
    Valid uvars vars facts -> forall hyps,
    Forall (Provable uvars vars) hyps ->
    Valid uvars vars (P.(Learn) facts (typeof_env uvars) (typeof_env vars) hyps)
  ; Prove_correct : ProveOk Valid P.(Prove)
  }.

  Theorem Prove_concl P (Pok : ProverOk P)
  : forall (vars uvars : env typD)
           (sum : Facts P),
      Valid Pok uvars vars sum ->
      forall (goal : expr),
        Prove P sum (typeof_env uvars) (typeof_env vars) goal = true ->
        forall val,
          exprD uvars vars goal ty = Some val ->
          Provable' val.
  Proof.
    intros.
    specialize (@Pok.(Prove_correct) vars uvars sum H goal H0).
    rewrite H1. exact (fun x => x).
  Qed.

  (** Composite Prover **)
  Section composite.
    Variables pl pr : Prover.

    Definition composite_Prover : Prover :=
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

    Variable pl_correct : ProverOk pl.
    Variable pr_correct : ProverOk pr.

    Theorem composite_ProverOk : ProverOk composite_Prover.
    Proof.
      refine (
        {| Valid := fun uvars vars (facts : Facts composite_Prover) =>
             let (fl,fr) := facts in
             Valid pl_correct uvars vars fl /\ Valid pr_correct uvars vars fr
         |});
      (destruct pl_correct; destruct pr_correct; simpl;
       try destruct facts; intuition eauto).
      unfold ProveOk. destruct sum; intuition.
      consider (Prove pl f (typeof_env uvars) (typeof_env vars) goal); intros.
      { eapply Prove_correct0; eassumption. }
      { eapply Prove_correct1; eassumption. }
    Qed.
  End composite.
End proverI.
