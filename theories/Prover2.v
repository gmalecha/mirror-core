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
  Variable typD : list Type -> typ -> Type.
  Context {RType_typ : RType typD}.
  Variable expr : Type.
  Context {Expr_expr : Expr typD expr}.
  Context {ty : typ}.
  Variable Provable' : typD nil ty -> Prop.

  Let Provable us vs e :=
    match exprD us vs e ty with
      | None => False
      | Some p => Provable' p
    end.

  Record Prover : Type :=
  { Facts : Type
  ; Summarize : tenv typ -> tenv typ -> list expr -> Facts
  ; Learn : Facts -> tenv typ -> tenv typ -> list expr -> Facts
  ; Prove : Facts -> tenv typ -> tenv typ -> expr -> bool
  }.

  Definition ProveOk (summary : Type)
    (Valid : forall tus tvs : tenv typ, summary -> ResType typD tus tvs Prop)
    (prover : summary -> tenv typ -> tenv typ -> expr -> bool)
  : Prop :=
    forall tus tvs sum (goal : expr),
      prover sum tus tvs goal = true ->
      (forall sumD goalD,
         Valid tus tvs sum = Some sumD ->
         exprD' tus tvs goal ty = Some goalD ->
         forall (us : HList.hlist (typD nil) tus)
                (vs : HList.hlist (typD nil) tvs),
           sumD us vs ->
           Provable' (goalD us vs)).

  Record ProverOk (P : Prover) : Type :=
  { factsD : forall tus tvs : tenv typ, Facts P -> ResType typD tus tvs Prop
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
    : ProveOk factsD (@Prove P)
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

    Opaque mapT.

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
