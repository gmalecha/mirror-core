Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SymI.
Require Import MirrorCore.EProver.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.LemmaExt.
Require Import MirrorCore.Ext.ExprSubst.
Require Import MirrorCore.Ext.ExprUnifySyntactic.
Require Import MirrorCore.Ext.SymEnv.
Require Import MirrorCore.provers.AssumptionProver.
Require Import MirrorCore.Subst.FastSubst.
Require Import Examples.Auto.AutoProver2.

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

Definition ts : types :=
  Eval compute in list_to_types (@Some Type nat :: nil).

Definition fs : functions ts :=
  Eval simpl in from_list
                  ((@F ts 0 (tyArr (tyType 1) tyProp) Even) ::
                   (@F ts 0 (tyType 1) O) ::
                   (@F ts 0 (tyArr (tyType 1) (tyType 1)) S) ::
                   (@F ts 0 (tyArr (tyType 1) (tyArr (tyType 1) (tyType 1))) plus) ::
                   (@F ts 0 (tyArr (tyType 1) (tyArr (tyType 1) (tyType 1))) minus) ::
                   nil).

Fixpoint makeNat (n : nat) : expr func :=
  match n with
    | 0 => Inj (FRef 2 nil)
    | S n => App (Inj (FRef 3 nil)) (makeNat n)
  end.

Let RSym_func : RSym (typD ts) func := @RSym_func ts fs.
Local Existing Instance RSym_func.

Let Expr_expr := Expr_expr RSym_func.
Local Existing Instance RSym_func.

Definition lem_0 : lemma func (expr func) :=
  Eval simpl makeNat in
    {| vars := nil ; premises := nil ; concl := App (Inj (FRef 1 nil)) (makeNat 0) |}.

Definition lem_SS : lemma func (expr func) :=
  {| vars := tyType 1 :: nil
     ; premises := App (Inj (FRef 1 nil)) (Var 0) :: nil
     ; concl := App (Inj (FRef 1 nil))
                    (App (Inj (FRef 3 nil)) (App (Inj (FRef 3 nil)) (Var 0)))
  |}.

Definition lem_plus : lemma func (expr func) :=
  {| vars := tyType 1 :: tyType 1 :: nil
   ; premises := App (Inj (FRef 1 nil)) (Var 0) ::
                 App (Inj (FRef 1 nil)) (Var 1) :: nil
   ; concl := App (Inj (FRef 1 nil))
                  (App (App (Inj (FRef 4 nil)) (Var 0)) (Var 1))
  |}.

Definition lem_minus : lemma func (expr func) :=
  {| vars := tyType 1 :: tyType 1 :: nil
   ; premises := App (Inj (FRef 1 nil)) (Var 0) ::
                 App (Inj (FRef 1 nil)) (Var 1) :: nil
   ; concl := App (Inj (FRef 1 nil))
                  (App (App (Inj (FRef 5 nil)) (Var 0)) (Var 1))
  |}.


Definition evenHints : Hints func :=
  {| Apply := lem_0 :: lem_SS :: lem_plus :: lem_minus :: nil
   ; Extern := from_Prover (@assumptionProver _ (expr func) _)
  |}.

Theorem evenHintsOk : @HintsOk _ _ _ evenHints.
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
    assert (ExprI.ExprOk Expr_expr) by admit.
    generalize (@assumptionProver_correct typ (typD ts) _ (expr func) _ _ _ _ H).
    unfold ExprProp.Provable_val, TypInstance0_tyProp.
    simpl. unfold Iso.soutof, Iso.outof, Iso.siso.
    simpl. auto. }
Qed.

Axiom SubstOk_fast_subst : @SubstI2.SubstOk _ _ _ _ _ (@Subst_fast_subst (expr func)).

Theorem Apply_auto_prove (fuel : nat) hints (Hok : HintsOk _ hints)
: forall facts (us vs : EnvI.env (typD ts)) goal s',
    @auto_prove ts func _ (fast_subst _) (@Subst_fast_subst _)
                (@SubstUpdate_fast_subst _ (@get_mentions_instantiate _) (@instantiate _))
                hints
                fuel facts
                (EnvI.typeof_env us) (EnvI.typeof_env vs) goal
                (fast_subst_empty _) = Some s' ->
    @SubstI2.substD _ _ _ _ _ _ SubstOk_fast_subst us vs s' ->
    match exprD us vs goal tyProp with
      | None => True
      | Some P => P
    end.
Proof.
Admitted.

Goal Even 0.
Proof.
  pose (goal := App (Inj (FRef 1 nil)) (makeNat 0)).
  change match exprD (E := Expr_expr) nil nil goal tyProp with
           | None => True
           | Some P => P
         end.
  eapply (@Apply_auto_prove 100 evenHints evenHintsOk
                            (evenHints.(Extern).(Summarize) nil nil nil)).
  compute. reflexivity.
  admit. (* compute. auto. *)
Qed.

(*
Goal Even 2.
Proof.
  pose (goal := App (Inj (FRef 1 nil)) (makeNat 2)).
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
  pose (goal := App (Inj (FRef 1 nil)) (makeNat 200)).
  change match exprD (E := Expr_expr) nil nil goal tyProp with
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
  admit.
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

Definition seven : expr func -> expr func := 
  App (Inj (FRef 1 nil)).
Definition splus (l r : expr func) : expr func := App (App (Inj (FRef 4 nil)) l) r.

Goal Even (0 + 0).
Proof.
  pose (goal := seven (splus (makeNat 0) (makeNat 0))).
  (** This is problematic because it is going to actually compute 600? **)
  Time change match exprD (E := Expr_expr) nil nil goal tyProp with
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
  admit.
Qed.

Goal Even ((200 + 200) + 200).
Proof.
  pose (goal := seven (splus (splus (makeNat 200) (makeNat 200)) (makeNat 200))).
  (** This is problematic because it is going to actually compute 600? **)
  Time change match exprD (E := Expr_expr) nil nil goal tyProp with
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
  admit.
Qed.
