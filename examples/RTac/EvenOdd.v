Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.RTac.RTac.
Require McExamples.Simple.Simple.
Require Import MirrorCore.syms.SymEnv.


Inductive Even : nat -> Prop :=
| E0 : Even 0
| EO : forall n, Odd n -> Even (S n)
with Odd : nat -> Prop :=
| OE : forall n, Even n -> Odd (S n).

Let typ := Simple.typ.
Let func := SymEnv.func.
Let tyNat := Simple.tyNat.
Let tyProp := Simple.tyProp.
Let tyArr := Simple.tyArr.

Definition args : functions _ :=
  from_list ({| ftype := tyNat ; fdenote := 0 |} ::
             {| ftype := tyArr tyNat tyNat ; fdenote := S |} ::
             {| ftype := tyArr tyNat tyProp ; fdenote := Even |} ::
             {| ftype := tyArr tyNat tyProp ; fdenote := Odd |} :: nil).

Let Zero_syn : expr typ func := ExprCore.Inj 1%positive.
Let S_syn : expr typ func := ExprCore.Inj 2%positive.
Let Even_syn : expr typ func := ExprCore.Inj 3%positive.
Let Odd_syn : expr typ func := ExprCore.Inj 4%positive.

Definition E0_syn : Lemma.lemma typ (expr typ func) (expr typ func) :=
{| Lemma.vars := nil
 ; Lemma.premises := nil
 ; Lemma.concl := App Even_syn Zero_syn
 |}.

Definition EO_syn : Lemma.lemma typ (expr typ func) (expr typ func) :=
{| Lemma.vars := tyNat :: nil
 ; Lemma.premises := App Odd_syn (ExprCore.Var 0) :: nil
 ; Lemma.concl := App Even_syn (App S_syn (ExprCore.Var 0))
 |}.

Definition OE_syn : Lemma.lemma typ (expr typ func) (expr typ func) :=
{| Lemma.vars := tyNat :: nil
 ; Lemma.premises := App Even_syn (ExprCore.Var 0) :: nil
 ; Lemma.concl := App Odd_syn (App S_syn (ExprCore.Var 0))
 |}.

Local Existing Instance Simple.RType_typ.
Local Instance RSym_func : RSym func := @RSym_func _ _ args.

Local Instance Expr_expr : Expr _ (expr typ func) := @Expr_expr typ func _ _ _.
Local Instance ExprOk_expr : @ExprOk _ _ (expr typ func) _ := @ExprOk_expr typ func _ _ _ _ _ _.


Local Instance ReifiedLemma_OE
: @ReifiedLemma typ (expr typ func) _ _ _ OE_syn :=
{ ReifiedLemma_proof := OE }.

Local Instance ReifiedLemma_EO
: @ReifiedLemma typ (expr typ func) _ _ _ EO_syn :=
{ ReifiedLemma_proof := EO }.

Local Instance ReifiedLemma_E0
: @ReifiedLemma typ (expr typ func) _ _ _ E0_syn :=
{ ReifiedLemma_proof := E0 }.

(*
Definition subst :=
  FMapSubst.SUBST.raw (expr typ func).
Local Instance Subst_subst : SubstI.Subst subst (expr typ func)
  := FMapSubst.SUBST.Subst_subst _.
Local Instance SubstUpdate_subst : SubstI.SubstUpdate subst (expr typ func)
  := @FMapSubst.SUBST.SubstUpdate_subst _ _.
*)

Let APPLY_no_minify (l : Lemma.lemma typ (expr typ func) (expr typ func))
: rtac typ (expr typ func) :=
  (@APPLY typ (expr typ func) _ _ _ _
          (fun subst _ _ => @exprUnify subst typ _ Simple.RType_typ _ _ _ _ 10) l).


Let APPLY (l : Lemma.lemma typ (expr typ func) (expr typ func)) : rtac typ (expr typ func) :=
  THEN (APPLY_no_minify l) (@MINIFY _ _ _ _ _).

Theorem APPLY_sound
: forall l,
    @Lemma.lemmaD _ _ _ _ _ (exprD'_typ0 (T:=Prop)) _ nil nil l ->
    rtac_sound (APPLY l).
Proof.
  intros. unfold APPLY, APPLY_no_minify.
  rtac_derive_soundness_default; eauto with typeclass_instances.
  eapply APPLY_sound; eauto with typeclass_instances.
  2: constructor; assumption.
  intros. eapply exprUnify_sound; eauto with typeclass_instances.
Qed.

Instance RtacSound l (RL : ReifiedLemma l) : RtacSound (APPLY l) :=
{ RtacSound_proof := APPLY_sound l (@ReifiedLemma_proof _ _ _ _ _ _ _) }.

Definition even_odd_tac : rtac typ (expr typ func) :=
  REPEAT 2000 (FIRST [ APPLY EO_syn
                     | APPLY OE_syn
                     | APPLY E0_syn ]).

Definition App' : expr typ func -> expr typ func -> expr typ func :=
  @App _ _.

Fixpoint build_n (n : nat) : expr typ func :=
  match n with
    | 0 => Zero_syn
    | S n => App' S_syn (build_n n)
  end.

Definition runRTac_empty_goal (tac : rtac typ (expr typ func))
           (goal : expr typ func)  :=
  (@runOnGoals _ _ _ _ tac)
        nil nil 0 0 _ (@TopSubst _ _ nil nil)
        (@GGoal typ (expr typ func) goal).

Existing Class rtac_sound.
Existing Instance RtacSound_proof.

Theorem even_odd_tac_sound
: rtac_sound even_odd_tac.
Proof.
  unfold even_odd_tac.
  rtac_derive_soundness_default.
Qed.

(*Time Eval vm_compute in runRTac_empty_goal even_odd_tac (App Even_syn (build_n 1024)). *)

Definition GoalD (us vs : env) (g : Goal typ (expr typ func)) : Prop :=
  let (tus, us0) := split_env us in
  let (tvs, vs0) := split_env vs in
  match @goalD typ (expr typ func) _ _ _ tus tvs g with
    | Some P => P us0 vs0
    | None => True
  end.

Definition full_solved : @Result typ (expr typ func) (CTop nil nil) :=
  Solved (TopSubst (expr typ func) nil nil).

Theorem runGoal_sound
: forall e,
    runRTac_empty_goal even_odd_tac e = full_solved ->
    GoalD nil nil (GGoal e).
Proof.
  unfold full_solved, runRTac_empty_goal. intros.
  generalize (@rtac_Solved_closed_soundness typ (expr typ func) _ _ _ even_odd_tac even_odd_tac_sound nil nil e).
  unfold runRtac. simpl in H. simpl.
  intro. apply H0 in H; clear H0.
  unfold GoalD. simpl. unfold Ctx.propD, propD in *.
  simpl in *. exact H.
Defined.

(*
Goal Even 4.
  Time repeat constructor.
Time Qed.
*)

Require Import MirrorCore.Reify.Reify.

Reify Declare Patterns patterns_simple := (expr typ func).
Reify Declare Syntax reify_simple :=
  { (@Patterns.CFirst _ ((@Patterns.CPatterns (expr typ func) patterns_simple) ::
                         (@Patterns.CApp (expr typ func) (App')) :: nil))
  }.

Reify Pattern patterns_simple += (@RExact _ O) => (Zero_syn).
Reify Pattern patterns_simple += (@RExact _ S) => (S_syn).
Reify Pattern patterns_simple += (@RExact _ Even) => (Even_syn).
Reify Pattern patterns_simple += (@RExact _ Odd) => (Odd_syn).

Ltac solve_it trm :=
  let k e :=
    pose (eV := e) ;
    (change (GoalD nil nil (GGoal eV))) ;
    apply (@runGoal_sound eV) ; vm_compute; reflexivity
  in
  reify_expr reify_simple k [[ True ]] [[ trm ]].


Ltac solve_it' trm :=
  let k eV :=
    (change (GoalD nil nil (GGoal eV))) ;
    apply (@runGoal_sound eV) ; vm_compute; reflexivity
  in
  reify_expr_bind reify_simple k [[ True ]] [[ trm ]].

Ltac solve_it'' trm :=
  let k e :=
    pose (eV := e) ;
    (change (GoalD nil nil (GGoal eV))) ;
    apply (@runGoal_sound eV) ; vm_compute; reflexivity
  in
  reify_expr reify_simple k [[ True ]] [[ trm ]].

Ltac solve_it''' trm :=
  let k e :=
    (change (GoalD nil nil (GGoal e))) ;
    apply (@runGoal_sound e) ; vm_compute; reflexivity
  in
  reify_expr reify_simple k [[ True ]] [[ trm ]].

Definition proof : Even 4.
  Time  match goal with
    | |- ?X =>
      solve_it' X
  end.
Defined.