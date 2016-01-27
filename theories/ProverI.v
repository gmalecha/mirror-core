(** Provers that establish [expr]-encoded facts.
 ** They can also choose particular substitutions.
 **)
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.ExprProp.

Set Implicit Arguments.
Set Strict Implicit.

Section proverI.
  Context {typ : Type}.
  Context {RType_typ : RType typ}.
  Variable expr : Type.
  Context {Expr_expr : Expr _ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.

  Record Prover : Type :=
  { Facts : Type
  ; Summarize : tenv typ -> tenv typ -> list expr -> Facts
  ; Learn : Facts -> tenv typ -> tenv typ -> list expr -> Facts
  ; Prove : Facts -> tenv typ -> tenv typ -> expr -> bool
  }.

  Definition ProveOk (summary : Type)
    (Valid : forall tus tvs, summary -> option (exprT tus tvs Prop))
    (prover : summary -> tenv typ -> tenv typ -> expr -> bool)
  : Prop :=
    forall tus tvs sum (goal : expr),
      prover sum tus tvs goal = true ->
      (forall sumD goalD,
         Valid tus tvs sum = Some sumD ->
         Provable tus tvs goal = Some goalD ->
         forall (us : HList.hlist typD tus)
                (vs : HList.hlist typD tvs),
           sumD us vs ->
           goalD us vs).

  Record ProverOk (P : Prover) : Type :=
  { factsD : forall tus tvs, Facts P -> option (exprT tus tvs Prop)
  ; factsD_weaken
    : forall tus tvs f sumD,
        factsD tus tvs f = Some sumD ->
        forall tus' tvs',
        exists sumD',
             factsD (tus ++ tus') (tvs ++ tvs') f = Some sumD'
          /\ forall us vs us' vs',
               sumD us vs <->
               sumD' (HList.hlist_app us us') (HList.hlist_app vs vs')
  ; Summarize_sound
    : forall tus tvs hyps premD,
        AllProvable tus tvs hyps = Some premD ->
        exists sumD,
          factsD tus tvs (Summarize P tus tvs hyps) = Some sumD /\
          forall us vs,
            premD us vs ->
            sumD us vs
  ; Learn_sound
    : forall tus tvs hyps premD sum sumD,
        factsD tus tvs sum = Some sumD ->
        AllProvable tus tvs hyps = Some premD ->
        exists sumD',
          factsD tus tvs (Learn P sum tus tvs hyps) = Some sumD' /\
          forall us vs,
            premD us vs ->
            sumD us vs ->
            sumD' us vs
  ; Prove_sound
    : ProveOk factsD (@Prove P)
  }.

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
         if @Prove pl fl uenv venv goal then true
         else @Prove pr fr uenv venv goal
    |}.

    Variable pl_correct : ProverOk pl.
    Variable pr_correct : ProverOk pr.

    Theorem composite_ProverT_correct : ProverOk composite_Prover.
    Proof.
      refine (
        {| factsD := fun uvars vars (facts : Facts composite_Prover) =>
             let (fl,fr) := facts in
             match factsD pl_correct uvars vars fl
                 , factsD pr_correct uvars vars fr
             with
               | Some l , Some r => Some (fun us vs => l us vs /\ r us vs)
               | _ , _ => None
             end
         |}).
      { intros. forward. inv_all; subst.
        eapply factsD_weaken with (tus' := tus') (tvs' := tvs') in H0.
        eapply factsD_weaken with (tus' := tus') (tvs' := tvs') in H1.
        forward_reason. Cases.rewrite_all_goal.
        eexists; split; eauto. intros. simpl.
        rewrite <- H2. rewrite H1. reflexivity. }
      { simpl; intros.
        specialize (@Summarize_sound _ pl_correct _ _ _ _ H).
        specialize (@Summarize_sound _ pr_correct _ _ _ _ H).
        intros; forward_reason. Cases.rewrite_all_goal.
        eexists; split; eauto.
        intros. simpl. split; eauto. }
      { simpl; intros. forward; inv_all; subst.
        forward_reason; inv_all; subst.
        specialize (@Learn_sound _ pl_correct _ _ _ _ _ _ H1 H0).
        specialize (@Learn_sound _ pr_correct _ _ _ _ _ _ H2 H0).
        intros. forward_reason.
        Cases.rewrite_all_goal.
        eexists; split; eauto. intros.
        simpl. intuition. }
      { red. simpl. intros.
        forward. subst.
        consider (Prove pl f tus tvs goal).
        { intros; inv_all; subst.
          specialize (@Prove_sound _ pl_correct _ _ _ _ H _ _ H3 H1).
          intros; forward_reason; eauto. }
        { intros; inv_all; subst.
          specialize (@Prove_sound _ pr_correct _ _ _ _ H0 _ _ H4 H1).
          intros; forward_reason; eauto. } }
    Qed.
  End composite.

End proverI.

Arguments Prover typ expr.
Arguments composite_Prover {typ} {expr} _ _.
