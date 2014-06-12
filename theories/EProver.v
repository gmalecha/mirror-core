Require Import Coq.Lists.List.
Require Import ExtLib.Tactics.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SubstI.

Set Implicit Arguments.
Set Strict Implicit.

(** Provers that establish [expr]-encoded facts.
 ** They can also choose particular substitutions.
 **)
Section proverI.
  Context {typ : Type}.
  Context {RType_typ : RType typ}.
  Variable expr : Type.
  Context {Expr_expr : Expr _ expr}.
  Context {ty : typ}.
  Variable Provable' : typD nil ty -> Prop.

  Let Provable us vs e :=
    match exprD us vs e ty with
      | None => False
      | Some p => Provable' p
    end.

  Record EProver : Type :=
  { Facts : Type
  ; Summarize : tenv typ -> tenv typ -> list expr -> Facts
  ; Learn : Facts -> tenv typ -> tenv typ -> list expr -> Facts
  ; Prove : forall (subst : Type) {S : Subst subst expr},
              Facts -> tenv typ -> tenv typ -> subst -> expr -> option subst
  }.

  Definition EProveOk (summary : Type)
             (subst : Type) (Ssubst : Subst subst expr)
             (SsubstOk : @SubstOk subst expr typ _ _ _)
    (valid : env nil -> env nil -> summary -> Prop)
    (prover : summary -> tenv typ -> tenv typ -> subst -> expr -> option subst) : Prop :=
    forall uvars vars sum,
      valid uvars vars sum ->
      forall (goal : expr) (sub sub' : subst),
        prover sum (typeof_env uvars) (typeof_env vars) sub goal = Some sub' ->
        WellTyped_subst (typeof_env uvars) (typeof_env vars) sub ->
        substD uvars vars sub' ->
        match exprD uvars vars goal ty with
          | None => True
          | Some val => Provable' val /\ substD uvars vars sub
        end.

  Record EProverOk (P : EProver) : Type :=
  { Valid : env nil -> env nil -> Facts P -> Prop
  ; Valid_weaken : forall u g f ue ge,
    Valid u g f -> Valid (u ++ ue) (g ++ ge) f
  ; Summarize_correct : forall (uvars vars : env nil) (hyps : list expr),
    Forall (Provable uvars vars) hyps ->
    Valid uvars vars (Summarize P (typeof_env uvars) (typeof_env vars) hyps)
  ; Learn_correct : forall uvars vars facts,
    Valid uvars vars facts -> forall hyps,
    Forall (Provable uvars vars) hyps ->
    Valid uvars vars (P.(Learn) facts (typeof_env uvars) (typeof_env vars) hyps)
  ; Prove_correct : forall subst (Ssubst : Subst subst expr)
                      (Sok : SubstOk _ _),
                      EProveOk Sok Valid (@Prove P subst Ssubst)
  }.

  Theorem Prove_concl P (Pok : EProverOk P)
  : forall subst (Ssubst : Subst subst expr)
           (Sok : SubstOk _ _)
           (vars uvars : env nil)
           (sum : Facts P),
      Valid Pok uvars vars sum ->
      forall (goal : expr) (sub sub' : subst),
        Prove P sum (typeof_env uvars) (typeof_env vars) sub goal = Some sub' ->
        WellTyped_subst (typeof_env uvars) (typeof_env vars) sub ->
        substD uvars vars sub' ->
        forall val,
          exprD uvars vars goal ty = Some val ->
          Provable' val /\ substD uvars vars sub.
  Proof.
    intros.
    specialize (@Pok.(Prove_correct) Sok uvars vars sum H goal sub H0 H1 H2).
    rewrite H3. exact (fun x => x).
  Qed.

  (** Composite Prover **)
  Section composite.
    Variables pl pr : EProver.

    Definition composite_EProver : EProver :=
    {| Facts := Facts pl * Facts pr
     ; Summarize := fun uenv venv hyps =>
         (pl.(Summarize) uenv venv hyps, pr.(Summarize) uenv venv hyps)
     ; Learn := fun facts uenv venv hyps =>
         let (fl,fr) := facts in
         (pl.(Learn) fl uenv venv hyps, pr.(Learn) fr uenv venv hyps)
     ; Prove := fun subst Subst facts uenv venv s goal =>
         let (fl,fr) := facts in
         match @Prove pl subst Subst fl uenv venv s goal with
           | Some s' => Some s'
           | None => @Prove pr subst Subst fr uenv venv s goal
         end
    |}.

    Variable pl_correct : EProverOk pl.
    Variable pr_correct : EProverOk pr.

    Theorem composite_ProverT_correct : EProverOk composite_EProver.
    Proof.
      refine (
        {| Valid := fun uvars vars (facts : Facts composite_EProver) =>
             let (fl,fr) := facts in
             Valid pl_correct uvars vars fl /\ Valid pr_correct uvars vars fr
         |});
      try solve [ destruct pl_correct; destruct pr_correct; simpl;
       try destruct facts; intuition eauto ].
      intros.
      unfold EProveOk. destruct sum.
      intros.
      destruct H. simpl in H0.
      forward.
      match goal with
        | H : match ?X with _ => _ end = _ |- _ =>
          consider X; intros
      end; inv_all; subst.
      { eapply (Prove_concl pl_correct); try eassumption. }
      { eapply (Prove_concl pr_correct); try eassumption. }
    Qed.
  End composite.

  (** From non-EProvers **)
  Section non_eprover.
    Require Import MirrorCore.Prover.
    Variables p : Prover typ expr.

    Definition from_Prover : EProver :=
      @Build_EProver
        p.(Facts)
        p.(Summarize)
        p.(Learn)
        (fun subst Subst facts uenv venv s goal =>
           if p.(Prove) facts uenv venv goal then Some s else None).

    Variable p_correct : ProverOk Provable' p.

    Theorem from_ProverT_correct : EProverOk from_Prover.
    Proof.
      refine (
          @Build_EProverOk from_Prover
                                  p_correct.(Valid) _ _ _ _);
      try solve [ destruct p_correct; simpl; intuition eauto ].
      unfold EProveOk, ProveOk in *.
      intros. simpl in H0.
      forward. inv_all; subst.
      split; eauto.
      eapply Prover.Prove_concl; eauto.
    Qed.
  End non_eprover.
End proverI.

Arguments EProver typ expr.
Arguments composite_EProver {typ} {expr} _ _.
Arguments from_Prover {typ} {expr} _.