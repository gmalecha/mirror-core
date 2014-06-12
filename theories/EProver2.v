Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Tactics.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SubstI3.

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
             (SsubstOk : @SubstOk subst typ _ expr _ _)
    (Valid : forall tus tvs : tenv typ, summary -> ResType tus tvs Prop)
    (prover : summary -> tenv typ -> tenv typ -> subst -> expr -> option subst)
  : Prop :=
    forall tus tvs sum (goal : expr) (sub sub' : subst),
      prover sum tus tvs sub goal = Some sub' ->
      WellFormed_subst sub ->
      WellFormed_subst sub' /\
      (forall sumD subD goalD,
         Valid tus tvs sum = Some sumD ->
         substD tus tvs sub = Some subD ->
         exprD' tus tvs goal ty = Some goalD ->
         exists subD',
           substD tus tvs sub' = Some subD' /\
           forall (us : HList.hlist (typD nil) tus)
                  (vs : HList.hlist (typD nil) tvs),
             sumD us vs ->
             subD' us vs ->
             subD us vs /\
             Provable' (goalD us vs)).

  Record EProverOk (P : EProver) : Type :=
  { factsD : forall tus tvs : tenv typ, Facts P -> ResType tus tvs Prop
  ; factsD_weakenU
    : forall tus tvs f sumD,
        factsD tus tvs f = Some sumD ->
        forall tus',
        exists sumD',
             factsD (tus ++ tus') tvs f = Some sumD'
          /\ forall us vs us',
               sumD us vs <->
               sumD' (HList.hlist_app us us') vs
  ; factsD_weakenV
    : forall tus tvs f sumD,
        factsD tus tvs f = Some sumD ->
        forall tvs',
        exists sumD',
             factsD tus (tvs ++ tvs') f = Some sumD'
          /\ forall us vs vs',
               sumD us vs <->
               sumD' us (HList.hlist_app vs vs')
  ; Summarize_sound
    : forall tus tvs hyps premD,
        mapT (T := list) (F := option) (fun e => exprD' tus tvs e ty) hyps = Some premD ->
        exists sumD,
          factsD tus tvs (Summarize P tus tvs hyps) = Some sumD /\
          forall us vs,
            Forall (fun x => Provable' (x us vs)) premD ->
            sumD us vs
  ; Learn_sound
    : forall tus tvs hyps premD sum sumD,
        factsD tus tvs sum = Some sumD ->
        mapT (T := list) (F := option) (fun e => exprD' tus tvs e ty) hyps = Some premD ->
        exists sumD',
          factsD tus tvs (Learn P sum tus tvs hyps) = Some sumD' /\
          forall us vs,
            Forall (fun x => Provable' (x us vs)) premD ->
            sumD us vs ->
            sumD' us vs
  ; Prove_sound
    : forall subst (Ssubst : Subst subst expr)
             (Sok : SubstOk _ _),
        EProveOk Sok factsD (@Prove P subst Ssubst)
  }.

(*
  Theorem Prove_concl P (Pok : EProverOk P)
  : forall subst (Ssubst : Subst subst expr)
           (Sok : SubstOk _ _)
           (vars uvars : env typD)
           (sum : Facts P),
      forall (goal : expr) (sub sub' : subst),
        Prove P sum (typeof_env uvars) (typeof_env vars) sub goal = Some sub' ->
        WellFormed_subst sub ->
        WellFormed_subst sub' /\
        (Valid Pok uvars vars sum ->
         WellTyped_subst (typeof_env uvars) (typeof_env vars) sub ->
         WellTyped_subst (typeof_env uvars) (typeof_env vars) sub' /\
         (substD uvars vars sub' ->
          forall val,
            exprD uvars vars goal ty = Some val ->
            Provable' val /\ substD uvars vars sub)).
  Proof.
    intros.
    destruct (@Pok.(Prove_correct) Sok uvars vars sum goal sub H H0).
    split; auto.
    intros. forward_reason. 
    split; auto.
    intros. forward_reason.
    rewrite H7 in *. assumption.
  Qed.
*)

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

    Opaque mapT.

    Theorem composite_ProverT_correct : EProverOk composite_EProver.
    Proof.
      refine (
        {| factsD := fun uvars vars (facts : Facts composite_EProver) =>
             let (fl,fr) := facts in
             match factsD pl_correct uvars vars fl
                 , factsD pr_correct uvars vars fr
             with
               | Some l , Some r => Some (fun us vs => l us vs /\ r us vs)
               | _ , _ => None
             end
         |}).
      { intros. forward. inv_all; subst.
        eapply factsD_weakenU with (tus' := tus') in H0.
        eapply factsD_weakenU with (tus' := tus') in H1.
        forward_reason. Cases.rewrite_all_goal.
        eexists; split; eauto. intros. simpl.
        rewrite <- H2. rewrite H1. reflexivity. }
      { intros. forward. inv_all; subst.
        eapply factsD_weakenV with (tvs' := tvs') in H0.
        eapply factsD_weakenV with (tvs' := tvs') in H1.
        forward_reason. Cases.rewrite_all_goal.
        eexists; split; eauto. intros. simpl.
        rewrite <- H2. rewrite <- H1. reflexivity. }
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
        consider (Prove pl f tus tvs sub goal).
        { intros; inv_all; subst.
          specialize (@Prove_sound _ pl_correct _ _ _ _ _ _ _ _ _ H H0).
          intros; forward_reason.
          split; auto. intros; forward_reason.
          forward. inv_all; subst.
          specialize (H3 _ _ _ eq_refl H4 H5).
          forward_reason. eexists; split; eauto.
          intros. eapply H7; intuition. }
        { intros; inv_all; subst.
          specialize (@Prove_sound _ pr_correct _ _ _ _ _ _ _ _ _ H1 H0).
          intros; forward_reason.
          split; auto. intros; forward_reason.
          forward. inv_all; subst.
          specialize (H7 _ _ _ eq_refl H5 H6).
          forward_reason. eexists; split; eauto.
          intros. eapply H8; intuition. } }
    Qed.
  End composite.

  (** From non-EProvers **)
  Section non_eprover.
    Require Import MirrorCore.Prover2.
    Variables p : @Prover typ expr.

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
                                  p_correct.(factsD) _ _ _ _ _);
      try solve [ destruct p_correct; simpl; intuition eauto ].
      unfold EProveOk, ProveOk in *.
      intros. simpl in H0.
      simpl in H. forward. inv_all; subst.
      split; auto. intros.
      eexists; split; eauto. intros. split; auto.
      eapply Prove_sound in H; eauto.
      eapply H; eauto.
    Qed.
  End non_eprover.

End proverI.

Arguments EProver typ expr.
Arguments composite_EProver {typ} {expr} _ _.
Arguments from_Prover {typ} {expr} _.
