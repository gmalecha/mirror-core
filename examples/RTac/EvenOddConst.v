Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.RTac.RTac.
Require McExamples.Simple.Simple.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.syms.SymSum.


Inductive Even : nat -> Prop :=
| E0 : Even 0
| EO : forall n, Odd n -> Even (S n)
with Odd : nat -> Prop :=
| OE : forall n, Even n -> Odd (S n).

Let typ := Simple.typ.
Let func := (SymEnv.func + nat)%type.
Let tyNat := Simple.tyNat.
Let tyProp := Simple.tyProp.
Let tyArr := Simple.tyArr.

Definition args : functions _ :=
  from_list ({| ftype := tyNat ; fdenote := 0 |} ::
             {| ftype := tyArr tyNat tyNat ; fdenote := S |} ::
             {| ftype := tyArr tyNat tyProp ; fdenote := Even |} ::
             {| ftype := tyArr tyNat tyProp ; fdenote := Odd |} :: nil).

Let Zero_syn : expr typ func := ExprCore.Inj (inl 1%positive).
Let S_syn : expr typ func := ExprCore.Inj (inl 2%positive).
Let Even_syn : expr typ func := ExprCore.Inj (inl 3%positive).
Let Odd_syn : expr typ func := ExprCore.Inj (inl 4%positive).

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
Definition RSym_nat : @RSym typ _ nat :=
{| typeof_sym := fun _ => Some tyNat
 ; symD := fun x => x
 ; sym_eqb := fun x y => Some (EqNat.beq_nat x y)
 |}.

Local Instance RSym_func : RSym func := RSym_sum (@RSym_func _ _ args) RSym_nat.
Local Instance RSymOk_func : RSymOk RSym_func := @RSymOk_sum _ _ _ _ _ _ _ _.
constructor. simpl.
intros. case PeanoNat.Nat.eqb_spec; auto.
Defined.

Local Instance Expr_expr : Expr _ (expr typ func) := @Expr_expr typ func _ _ _.
Local Instance ExprOk_expr : @ExprOk _ _ (expr typ func) _ := @ExprOk_expr typ func _ _ _ _ _ _.

Instance ReifiedLemma_E0_syn : ReifiedLemma E0_syn := { ReifiedLemma_proof := E0 }.
Instance ReifiedLemma_EO_syn : ReifiedLemma EO_syn := { ReifiedLemma_proof := EO }.
Instance ReifiedLemma_OE_syn : ReifiedLemma OE_syn := { ReifiedLemma_proof := OE }.

Let APPLY_no_minify (l : Lemma.lemma typ (expr typ func) (expr typ func)) : rtac typ (expr typ func) :=
  APPLY (fun subst _ _ => @exprUnify subst typ _ Simple.RType_typ _ _ _ _ 10) l.


Let APPLY (l : Lemma.lemma typ (expr typ func) (expr typ func)) : rtac typ (expr typ func) :=
  THEN (APPLY_no_minify l) MINIFY.

Theorem APPLY_sound
: forall l,
    ReifiedLemma l ->
    rtac_sound (APPLY l).
Proof.
  intros. unfold APPLY.
  eapply THEN_sound; eauto using MINIFY_sound with typeclass_instances.
  eapply APPLY_sound; eauto using exprUnify_sound, APPLY_sound, MINIFY_sound with typeclass_instances.
Qed.

Definition even_odd_tac : rtac typ (expr typ func) :=
  REPEAT 2000 (FIRST [ APPLY E0_syn
                     | APPLY EO_syn
                     | APPLY OE_syn ]).

Definition build_n (n : nat) : expr typ func := Inj (inr n).

Definition runRTac_empty_goal (tac : rtac typ (expr typ func))
           (goal : expr typ func)  :=
  (@runOnGoals _ _ _ _ tac)
        nil nil 0 0 _ (@TopSubst _ _ nil nil)
        (@GGoal typ (expr typ func) goal).

Theorem even_odd_tac_sound
: rtac_sound even_odd_tac.
Proof.
  eapply REPEAT_sound.
  eapply FIRST_sound.
  repeat first [ econstructor; [ eapply APPLY_sound; eauto with typeclass_instances | ]
               | solve [ constructor ] ].
Qed.

(*Time Eval vm_compute in runRTac_empty_goal even_odd_tac (App Even_syn (build_n 1024)).*)

Definition GoalD (us vs : env) (g : Goal typ (expr typ func)) : Prop :=
  let (tus, us0) := split_env us in
  let (tvs, vs0) := split_env vs in
  match @goalD typ (expr typ func) _ _ _ tus tvs g with
  | Some P => P us0 vs0
  | None => True
  end.

Definition full_solved : @Result typ (expr typ func) (CTop nil nil) :=
  Solved (TopSubst (expr typ func) nil nil).

Theorem generic_soundness
: forall tac,
    rtac_sound tac ->
    forall e,
    runRTac_empty_goal tac e = full_solved ->
    GoalD nil nil (GGoal e).
Proof.
  intros. unfold rtac_sound, runRTac_empty_goal in *.
  eapply H in H0.
  simpl in H0.
  destruct H0.
  - constructor.
  - constructor.
  - red. simpl.
    destruct (Ctx.propD nil nil e).
    + destruct H1; auto.
    + auto.
Qed.

Theorem runGoal_sound
: forall e,
    runRTac_empty_goal even_odd_tac e = full_solved ->
    GoalD nil nil (GGoal e).
Proof.
  intros; eapply generic_soundness; eauto using even_odd_tac_sound.
Qed.

Let Const (n : nat) : expr typ func := ExprCore.Inj (inr n).

Definition pE0_syn : Lemma.lemma typ (expr typ func) (expr typ func) :=
{| Lemma.vars := nil
 ; Lemma.premises := nil
 ; Lemma.concl := App Even_syn (Const 0)
 |}.

Definition pEO_syn (n : nat) : Lemma.lemma typ (expr typ func) (expr typ func) :=
{| Lemma.vars := nil
 ; Lemma.premises := App Odd_syn (Const n) :: nil
 ; Lemma.concl := App Even_syn (Const (S n))
 |}.

Definition pOE_syn (n : nat) : Lemma.lemma typ (expr typ func) (expr typ func) :=
{| Lemma.vars := nil
 ; Lemma.premises := App Even_syn (Const n) :: nil
 ; Lemma.concl := App Odd_syn (Const (S n))
 |}.

Instance ReifiedLemma_pE0_syn : ReifiedLemma pE0_syn := { ReifiedLemma_proof := E0 }.
Instance ReifiedLemma_pEO_syn n : ReifiedLemma (pEO_syn n) := { ReifiedLemma_proof := EO n }.
Instance ReifiedLemma_pOE_syn n : ReifiedLemma (pOE_syn n) := { ReifiedLemma_proof := OE n }.

Definition even_odd_tac_nrec (fuel : nat) : rtac typ (expr typ func) :=
  REC fuel
      (fun tac =>
         AT_GOAL (fun _ _ e =>
                    match e with
                    | App (ExprCore.Inj (inl 3%positive))
                          (ExprCore.Inj (inr 0)) =>
                      APPLY pE0_syn
                    | App (ExprCore.Inj (inl 3%positive))
                          (ExprCore.Inj (inr (S n))) =>
                      APPLY (pEO_syn n) ;; runOnGoals tac
                    | App (ExprCore.Inj (inl 4%positive))
                          (ExprCore.Inj (inr (S n))) =>
                      APPLY (pOE_syn n) ;; runOnGoals tac
                    | _ => FAIL
                    end))%rtac
       FAIL.

Fixpoint even_odd_tac_mf (n : nat) : rtac typ (expr typ func) :=
  match n with
  | 0 => APPLY pE0_syn
  | S n => FIRST [ APPLY (pEO_syn n) | APPLY (pOE_syn n) ] ;;
                 (fun x => runOnGoals (even_odd_tac_mf n) x)
  end%rtac.

Theorem runGoal_sound_mf
: forall n,
    runRTac_empty_goal (even_odd_tac_mf n) (App Even_syn (Const n)) = full_solved ->
    GoalD nil nil (GGoal (App Even_syn (Const n))).
Proof.
  intros; eapply generic_soundness; eauto.
  clear. induction n.
  { simpl. eapply APPLY_sound; eauto with typeclass_instances. }
  { Opaque FIRST. simpl.
    rtac_derive_soundness_default; eapply APPLY_sound; eauto with typeclass_instances. }
Qed.

Theorem runGoal_sound_nonrec
: forall n,
    runRTac_empty_goal (even_odd_tac_nrec n) (App Even_syn (Const n)) = full_solved ->
    GoalD nil nil (GGoal (App Even_syn (Const n))).
Proof.
  intros; eapply generic_soundness; eauto.
  unfold even_odd_tac_nrec.
  rtac_derive_soundness_default;
  eapply APPLY_sound; eauto with typeclass_instances.
Qed.

(*
Time Eval vm_compute in let n := 2000 in runRTac_empty_goal (even_odd_tac_mf n) (App Even_syn (Const n)).

Time Eval vm_compute in let n := 2000 in runRTac_empty_goal (even_odd_tac_nrec n) (App Even_syn (Const n)).
*)

Goal Even 512.
  Time match goal with
    | |- Even ?X =>
      pose (GoalD nil nil (GGoal (App Even_syn (Const X)))) ;
      apply (runGoal_sound_nonrec X); vm_compute; reflexivity
  end.
Time Qed.
