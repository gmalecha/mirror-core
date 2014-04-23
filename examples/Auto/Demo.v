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
Require Import MirrorCore.Ext.FMapSubst.
Require Import MirrorCore.Examples.Auto.AutoProver.

Set Implicit Arguments.
Set Strict Implicit.

Inductive Even : nat -> Prop :=
| Even_0 : Even 0
| Even_SS : forall n, Even n -> Even (S (S n)).

Definition ts : types :=
  Eval compute in list_to_types (@Some Type nat :: nil).

Definition fs : functions ts :=
  Eval simpl in from_list
                  ((@F ts 0 (tyArr (tyType 1) tyProp) Even) ::
                   (@F ts 0 (tyType 1) O) ::
                   (@F ts 0 (tyArr (tyType 1) (tyType 1)) S) ::
                   nil).

Fixpoint makeNat (n : nat) : expr func :=
  match n with
    | 0 => Inj (FRef 2 nil)
    | S n => App (Inj (FRef 3 nil)) (makeNat n)
  end.

Let RSym_func : RSym (typD ts) func := @RSym_func ts fs.
Local Existing Instance RSym_func.

Let Expr_expr : Expr (typD ts) (expr func) := @Expr_expr _ _ _.
Local Existing Instance Expr_expr.

Definition lem_0 : lemma func (expr func) :=
  Eval simpl makeNat in
    {| vars := nil ; premises := nil ; concl := App (Inj (FRef 1 nil)) (makeNat 0) |}.

Definition lem_SS : lemma func (expr func) :=
  {| vars := tyType 1 :: nil
     ; premises := App (Inj (FRef 1 nil)) (Var 0) :: nil
     ; concl := App (Inj (FRef 1 nil))
                    (App (Inj (FRef 3 nil)) (App (Inj (FRef 3 nil)) (Var 0)))
  |}.

Definition evenHints : Hints func :=
  {| Apply := lem_0 :: lem_SS :: nil
     ; Extern := from_Prover (@assumptionProver _ (expr func) _)
  |}.

Theorem evenHintsOk : @HintsOk _ _ _ evenHints.
Proof.
  constructor.
  { unfold evenHints; simpl.
    constructor.
    { exact Even_0. }
    { constructor.
      { exact Even_SS. }
      { constructor. } } }
  { unfold evenHints; simpl.
    eapply from_ProverT_correct; eauto with typeclass_instances.
    assert (ExprI.ExprOk Expr_expr) by admit.
    generalize (@assumptionProver_correct typ (typD ts) _ (expr func) _ _ _ _ H).
    unfold ExprProp.Provable_val, TypInstance0_tyProp.
    simpl. unfold Iso.soutof, Iso.outof, Iso.siso.
    simpl. auto. }
Qed.

Theorem Apply_auto_prove (fuel : nat) hints (Hok : HintsOk _ hints)
: forall facts (us vs : EnvI.env (typD ts)) goal s',
    @auto_prove ts func _ (SUBST.subst _) (SUBST.Subst_subst _) hints fuel facts
                (EnvI.typeof_env us) (EnvI.typeof_env vs) goal
                (SUBST.subst_empty _) = Some s' ->
    @SubstI.substD _ _ _ _ _ _  (SUBST.SubstOk_subst _) us vs s' ->
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
  compute. auto.
Qed.

Goal Even 2.
Proof.
  pose (goal := App (Inj (FRef 1 nil)) (makeNat 2)).
  change match exprD (E := Expr_expr) nil nil goal tyProp with
           | None => True
           | Some P => P
         end.
  eapply (@Apply_auto_prove 100 evenHints evenHintsOk
                            (evenHints.(Extern).(Summarize) nil nil nil)).
  compute. reflexivity.
  compute. auto.
Qed.

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
  Time vm_compute. reflexivity.
  compute. auto.
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
