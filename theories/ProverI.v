Require Import ExtLib.Tactics.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprProp.

Set Implicit Arguments.
Set Strict Implicit.

(** Provers that establish [expr]-encoded facts.
 ** They can also choose particular substitutions.
 **)
Section proverI.
  Context {typ : Type}.
  Context {RType_typ : RType typ}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Variable expr : tenv typ -> tenv typ -> typ -> Type.
  Context {Expr_expr : Expr _ expr}.

  Let tyProp := @typ0 _ _ _ Typ0_Prop.

  Record Prover : Type :=
  { Facts : tenv typ -> tenv typ -> Type
  ; Weaken : forall tus tvs tus' tvs', Facts tus tvs -> Facts (tus ++ tus') (tvs ++ tvs')
  ; Summarize : forall tus tvs : tenv typ, list (expr tus tvs tyProp) -> Facts tus tvs
  ; Learn : forall tus tvs : tenv typ, list (expr tus tvs tyProp) -> Facts tus tvs -> Facts tus tvs
  ; Prove : forall tus tvs : tenv typ, Facts tus tvs -> expr tus tvs tyProp -> bool
  }.

  Definition ProveOk (summary : tenv typ -> tenv typ -> Type)
    (Valid : forall tus tvs : tenv typ, summary tus tvs -> ResType tus tvs Prop)
    (prover : forall tus tvs : tenv typ, summary tus tvs -> expr tus tvs tyProp -> bool)
  : Prop :=
    forall tus tvs sum (goal : expr tus tvs tyProp),
      prover tus tvs sum goal = true ->
      (forall sumD goalD,
         Valid tus tvs sum = Some sumD ->
         Provable tus tvs goal = Some goalD ->
         forall (us : HList.hlist (typD nil) tus)
                (vs : HList.hlist (typD nil) tvs),
           sumD us vs ->
           goalD us vs).

  Record ProverOk (P : Prover) : Type :=
  { factsD : forall tus tvs : tenv typ, P.(Facts) tus tvs -> ResType tus tvs Prop
  ; factsD_weaken
    : forall tus tvs f sumD,
        factsD tus tvs f = Some sumD ->
        forall tus' tvs',
        exists sumD',
             factsD (tus ++ tus') (tvs ++ tvs') (P.(Weaken) tus tvs tus' tvs' f) = Some sumD'
          /\ forall us vs us' vs',
               sumD us vs <->
               sumD' (HList.hlist_app us us') (HList.hlist_app vs vs')
  ; Summarize_sound
    : forall tus tvs hyps premD,
        AllProvable tus tvs hyps = Some premD ->
        exists sumD,
          factsD tus tvs (P.(Summarize) hyps) = Some sumD /\
          forall us vs,
            premD us vs ->
            sumD us vs
  ; Learn_sound
    : forall tus tvs hyps premD sum sumD,
        factsD tus tvs sum = Some sumD ->
        AllProvable tus tvs hyps = Some premD ->
        exists sumD',
          factsD tus tvs (P.(Learn) hyps sum) = Some sumD' /\
          forall us vs,
            premD us vs ->
            sumD us vs ->
            sumD' us vs
  ; Prove_sound
    : ProveOk P.(Facts) factsD (@Prove P)
  }.

  (** Composite Prover **)
  Section composite.
    Variables pl pr : Prover.

    Definition composite_Prover : Prover :=
    {| Facts := fun tus tvs => pl.(Facts) tus tvs * pr.(Facts) tus tvs
     ; Weaken := fun tus tvs tus' tvs' facts =>
         let (fl,fr) := facts in
         (pl.(Weaken) tus tvs tus' tvs' fl,
          pr.(Weaken) tus tvs tus' tvs' fr)
     ; Summarize := fun uenv venv hyps =>
         (pl.(Summarize) hyps, pr.(Summarize) hyps)
     ; Learn := fun uenv venv hyps facts =>
         let (fl,fr) := facts in
         (pl.(Learn) hyps fl, pr.(Learn) hyps fr)
     ; Prove := fun uenv venv facts goal =>
         let (fl,fr) := facts in
         if pl.(Prove) fl goal then true
         else pr.(Prove) fr goal
    |}%type.

    Variable pl_correct : ProverOk pl.
    Variable pr_correct : ProverOk pr.

    Theorem composite_ProverT_correct : ProverOk composite_Prover.
    Proof.
      refine (
        {| factsD := fun uvars vars (facts : Facts composite_Prover uvars vars) =>
             let (fl,fr) := facts in
             match factsD pl_correct uvars vars fl
                 , factsD pr_correct uvars vars fr
             with
               | Some l , Some r => Some (fun us vs => l us vs /\ r us vs)
               | _ , _ => None
             end
         |}).
      { simpl. intros. forward. inv_all; subst.
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
        consider (Prove pl f goal).
        { intros; inv_all; subst.
          specialize (@Prove_sound _ pl_correct _ _ _ _ H _ _ H3 H1).
          intros; forward_reason; eauto. }
        { intros; inv_all; subst.
          specialize (@Prove_sound _ pr_correct _ _ _ _ H0 _ _ H4 H1).
          intros; forward_reason; eauto. } }
    Qed.
  End composite.

End proverI.

Arguments Prover typ {RType} {Typ0} expr : rename.
Arguments composite_Prover {typ} {RType} {Typ0} {expr} _ _ : rename.
