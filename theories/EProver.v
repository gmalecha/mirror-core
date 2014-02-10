Require Import Coq.Lists.List Coq.Bool.Bool.
Require Import ExtLib.Tactics.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprProp.
Require Import MirrorCore.Subst.

Set Implicit Arguments.
Set Strict Implicit.

(** Provers that establish [expr]-encoded facts.
 ** They can also choose particular substitutions.
 **)
Section proverI.
  Context {typ : Type}.
  Variable typD : list Type -> typ -> Type.
  Context {RType_typ : RType typD}.
  Variable expr : Type.
  Context {Expr_expr : Expr typD expr}.
  Context {typ0_prop : TypInstance0 typD Prop}.

  (** TODO:
   ** It may be adventageous to have a non-prop prover, to allow
   ** asking to prove equality facts.
   ** Additionally, restricting ourselves to goals denoted by
   ** [expr] implies that you are limited by what you can express.
   **)

  Record EProverT : Type :=
  { Facts : Type
  ; Summarize : tenv typ -> tenv typ -> list expr -> Facts
  ; Learn : Facts -> tenv typ -> tenv typ -> list expr -> Facts
  ; Prove : forall (subst : Type) {S : Subst subst expr},
              Facts -> tenv typ -> tenv typ -> subst -> expr -> option subst
  }.

  Definition EProverCorrect (summary : Type)
             (subst : Type) (Ssubst : Subst subst expr)
             (SsubstOk : @SubstOk subst expr typ _ _ _)
    (valid : env typD -> env typD -> summary -> Prop)
    (prover : summary -> tenv typ -> tenv typ -> subst -> expr -> option subst) : Prop :=
    forall vars uvars sum,
      valid uvars vars sum ->
      forall (goal : expr) (sub sub' : subst),
        prover sum (typeof_env uvars) (typeof_env vars) sub goal = Some sub' ->
        WellTyped_subst (typeof_env uvars) (typeof_env uvars) sub ->
        substD uvars vars sub' ->
        Safe_expr (typeof_env uvars) (typeof_env vars) goal (@typ0 _ _ _ typ0_prop) ->
        Provable typ0_prop uvars vars goal /\ substD uvars vars sub.

  Record EProverT_correct (P : EProverT) : Type :=
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
  ; Prove_correct : forall subst (Ssubst : Subst subst expr)
                      (Sok : SubstOk _ _),
                      EProverCorrect Sok Valid (@Prove P subst Ssubst)
  }.


  (** Composite Prover **)
  Section composite.
    Variables pl pr : EProverT.

    Definition composite_ProverT : EProverT :=
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

    Variable pl_correct : EProverT_correct pl.
    Variable pr_correct : EProverT_correct pr.

    Theorem composite_ProverT_correct : EProverT_correct composite_ProverT.
    Proof.
      refine (
        {| Valid := fun uvars vars (facts : Facts composite_ProverT) =>
             let (fl,fr) := facts in
             Valid pl_correct uvars vars fl /\ Valid pr_correct uvars vars fr
         |});
      (destruct pl_correct; destruct pr_correct; simpl;
       try destruct facts; intuition eauto).
      unfold EProverCorrect. destruct sum.
      intros.
      destruct H.
      match goal with
        | H : match ?X with _ => _ end = _ |- _ =>
          consider X; intros
      end; inv_all; subst.
      { eapply Prove_correct0; try eassumption. }
      { eapply Prove_correct1; try eassumption. }
    Qed.
  End composite.

  (** From non-EProvers **)
  Section non_eprover.
    Require Import MirrorCore.Prover.
    Variables p : @ProverT typ expr.

    Definition from_ProverT : EProverT :=
      @Build_EProverT
        p.(Facts)
        p.(Summarize)
        p.(Learn)
        (fun subst Subst facts uenv venv s goal =>
           if p.(Prove) facts uenv venv goal then Some s else None).

    Variable p_correct : ProverT_correct p.

    Theorem from_ProverT_correct : EProverT_correct from_ProverT.
    Proof.
      refine (
          @Build_EProverT_correct from_ProverT
                                  p_correct.(Valid) _ _ _ _);
      (destruct p_correct; simpl; intuition eauto).
      unfold EProverCorrect, ProverCorrect in *.
      intros.
      forward. inv_all; subst.
      split; eauto.
    Qed.
  End non_eprover.
End proverI.
