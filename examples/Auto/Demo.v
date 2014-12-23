Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SymI.
Require Import MirrorCore.EProverI.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprVariables.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.provers.AssumptionProver.
Require Import MirrorCore.Subst.FMapSubst.
Require Import MirrorCore.provers.AutoProver.
Require Import McExamples.Simple.Simple.

Set Implicit Arguments.
Set Strict Implicit.

Inductive Even : nat -> Prop :=
| Even_0 : Even 0
| Even_SS : forall n, Even n -> Even (S (S n)).

Theorem Even_plus : forall n m,
                      Even n -> Even m ->
                      Even (n + m).
Proof.
  induction 1; simpl; intros; auto.
  apply Even_SS. auto.
Qed.

Theorem Even_minus : forall n m,
                       Even n -> Even m ->
                       Even (n - m).
Proof.
  intros n m H. revert m.
  induction H; simpl; intros; auto.
  { constructor. }
  { destruct H0.
    { constructor. specialize (IHEven 0 Even_0).
      rewrite <- Minus.minus_n_O in IHEven. auto. }
    { eauto. } }
Qed.

Definition fs : @functions typ _ :=
  Eval simpl in from_list
                  ((@F typ _ (tyArr tyNat tyProp) (Even)) ::
                   (@F typ _ tyNat (O)) ::
                   (@F typ _  (tyArr tyNat tyNat) (S)) ::
                   (@F typ _  (tyArr tyNat (tyArr tyNat tyNat)) (plus)) ::
                   (@F typ _  (tyArr tyNat (tyArr tyNat tyNat)) (minus)) ::
                   nil).

Let func := SymEnv.func.

Fixpoint makeNat (n : nat) : expr typ func :=
  match n with
    | O => Inj (2)
    | S n => App (Inj 3) (makeNat n)
  end%positive.

Let RSym_func : @RSym typ _ func := SymEnv.RSym_func fs.
Local Existing Instance RSym_func.

Let Expr_expr : @ExprI.Expr typ _ (expr typ func) := Expr_expr.
Local Existing Instance Expr_expr.

Definition lem_0 : lemma typ (expr typ func) (expr typ func) :=
  Eval simpl makeNat in
    {| vars := nil ; premises := nil ; concl := App (Inj 1%positive) (makeNat 0) |}.

Definition lem_SS : lemma typ (expr typ func) (expr typ func) :=
  {| vars := tyNat :: nil
     ; premises := App (Inj 1%positive) (Var 0) :: nil
     ; concl := App (Inj 1%positive)
                    (App (Inj 3%positive) (App (Inj 3%positive) (Var 0)))
  |}.

Definition lem_plus : lemma typ (expr typ func) (expr typ func) :=
  {| vars := tyNat :: tyNat :: nil
   ; premises := App (Inj 1%positive) (Var 0) ::
                 App (Inj 1%positive) (Var 1) :: nil
   ; concl := App (Inj 1%positive)
                  (App (App (Inj 4%positive) (Var 0)) (Var 1))
  |}.

Definition lem_minus : lemma typ (expr typ func) (expr typ func) :=
  {| vars := tyNat :: tyNat :: nil
   ; premises := App (Inj 1%positive) (Var 0) ::
                 App (Inj 1%positive) (Var 1) :: nil
   ; concl := App (Inj 1%positive)
                  (App (App (Inj 5%positive) (Var 0)) (Var 1))
  |}.


Definition evenHints : Hints typ (expr typ func) :=
{| Apply := lem_0 :: lem_SS :: lem_plus :: lem_minus :: nil
 ; Extern := from_Prover (@assumptionProver _ (expr typ func) _)
 |}.

Instance ExprOk_expr : ExprI.ExprOk Expr_expr :=
  @ExprOk_expr _ _ _ _ _ _ _ _.

Theorem evenHintsOk : @HintsOk _ _ RType_typ _ _ _ evenHints.
Proof.
  constructor.
  { unfold evenHints; simpl.
    repeat (apply Forall_cons || apply Forall_nil).
    exact Even_0.
    exact Even_SS.
    exact Even_plus.
    exact Even_minus. }
  { unfold evenHints; simpl.
    eapply from_ProverT_correct; eauto with typeclass_instances.
    apply (@assumptionProver_correct typ _ (expr typ func) _ _ _ _ _). }
Qed.



Let subst := FMapSubst.SUBST.raw (expr typ func).
Local Instance Subst_subst : SubstI.Subst subst (expr typ func) := FMapSubst.SUBST.Subst_subst _.
Local Instance SubstUpdate_subst : SubstI.SubstUpdate subst (expr typ func) :=
  @FMapSubst.SUBST.SubstUpdate_subst _ _.

Local Instance SubstOk_fmap_subst : @SubstI.SubstOk _ _ _ _ _ _ Subst_subst :=
  @FMapSubst.SUBST.SubstOk_subst _ _ _ _ _.
Local Instance SubstUpdateOk_fmap_subst : SubstI.SubstUpdateOk _ _.
eapply (@FMapSubst.SUBST.SubstUpdateOk_subst _ _ _ _ _).
eauto with typeclass_instances.
Qed.

Require MirrorCore.Lambda.ExprUnify_simul.

Theorem Apply_auto_prove (fuel : nat) hints (Hok : HintsOk hints)
: forall facts (us vs : EnvI.env) goal s',
    @auto_prove typ (expr typ func) _ _ subst _ _ 
                hints
                (vars_to_uvars)
                (fun tus tvs under el er (t : typ) (sub : subst) =>
                   @ExprUnify_simul.exprUnify _ _ _ _ _ _ _ _ 10 tus tvs under sub el er t)
                (@instantiate typ func) fuel facts
                (EnvI.typeof_env us) (EnvI.typeof_env vs) goal
                (@SubstI.subst_empty _ _ _) = Some s' ->
    (let (tus,us) := EnvI.split_env us in
     let (tvs,vs) := EnvI.split_env vs in
     match @SubstI.substD _ _ _ _ _ _ _ tus tvs s' with
       | None => False
       | Some P => P us vs
     end) ->
    match @ExprI.exprD _ RType_typ _ _ us vs goal tyProp return Prop with
      | None => True
      | Some P => P
    end.
Proof.
Admitted.

Goal Even 0.
Proof.
  pose (goal := App (Inj 1%positive) (makeNat 0)).
  change match ExprI.exprD (Expr := Expr_expr) nil nil goal tyProp with
           | None => True
           | Some P => P
         end.
  eapply (@Apply_auto_prove 100 evenHints evenHintsOk
                            (evenHints.(Extern).(Summarize) nil nil nil)).
  compute. reflexivity.
  compute. auto.
Qed.

(*
Goal Even 2.
Proof.
  pose (goal := App (Inj 1%positive) (makeNat 2)).
  change match exprD nil nil goal tyProp with
           | None => True
           | Some P => P
         end.
  eapply (@Apply_auto_prove 100 evenHints evenHintsOk
                            (evenHints.(Extern).(Summarize) nil nil nil)).
  compute. reflexivity.
  compute. auto.
Qed.
*)

Goal Even 200.
Proof.
  pose (goal := App (Inj 1%positive) (makeNat 200)).
  change match ExprI.exprD (Expr := Expr_expr) nil nil goal tyProp with
           | None => True
           | Some P => P
         end.
  eapply (@Apply_auto_prove 101 evenHints evenHintsOk
                            (evenHints.(Extern).(Summarize) nil nil nil)).
  match goal with
    | |- ?X = Some ?Y =>
      let res := eval vm_compute in X in
                                     (etransitivity ; [ | exact (@eq_refl _ res) ])
  end.
  Time vm_compute; reflexivity.
  compute. reflexivity.
Qed.
(** vm_compute is still *very* slow for this!
 ** - Some optimizations might be possible
 **   - Make unification faster, e.g. special-case fully instantiated terms
 **     so you don't keep instantiating them.
 **   - eliminate fully instantiated unification variables
 **)

Goal Even 200.
Proof.
  Time eauto 200 using Even_0, Even_SS.
Qed.

Goal Even ((200 + 200) + 200).
Proof.
  Time eauto 400 using Even_0, Even_SS, Even_plus.
Qed.

Definition seven : expr typ func -> expr typ func := 
  App (Inj 1%positive).
Definition splus (l r : expr typ func) : expr typ func := App (App (Inj 4%positive) l) r.

Goal Even (0 + 0).
Proof.
  pose (goal := seven (splus (makeNat 0) (makeNat 0))).
  (** This is problematic because it is going to actually compute 600? **)
  Time change match ExprI.exprD (Expr := Expr_expr) nil nil goal tyProp with
                | None => True
                | Some P => P
              end.
  eapply (@Apply_auto_prove 2 evenHints evenHintsOk
                            (evenHints.(Extern).(Summarize) nil nil nil)).
  match goal with
    | |- ?X = Some ?Y =>
      let res := eval vm_compute in X in
      (etransitivity ; [ | exact (@eq_refl _ res) ])
  end.
  Time (vm_compute; reflexivity).
  compute. trivial.
Qed.

Goal Even ((200 + 200) + 200).
Proof.
  pose (goal := seven (splus (splus (makeNat 200) (makeNat 200)) (makeNat 200))).
  (** This is problematic because it is going to actually compute 600? **)
  Time change match ExprI.exprD (Expr := Expr_expr) nil nil goal tyProp with
                | None => True
                | Some P => P
              end.
  eapply (@Apply_auto_prove 203 evenHints evenHintsOk
                            (evenHints.(Extern).(Summarize) nil nil nil)).
  match goal with
    | |- ?X = Some ?Y =>
      let res := eval vm_compute in X in
      (etransitivity ; [ | exact (@eq_refl _ res) ])
  end.
  Time vm_compute; reflexivity.
  compute. trivial.
Qed.
