Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SymI.
Require Import MirrorCore.EProverI.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprVariables.
Require MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.provers.AssumptionProver.
Require Import MirrorCore.Subst.FMapSubst.
Require Import MirrorCore.provers.AutoProver.
Require Import McExamples.Simple.Simple.
Require Import McExamples.Simple.SimpleReify.

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

Reify Declare Patterns patterns_even := (expr typ func).
Reify Declare Syntax reify_even :=
  (@Patterns.CFirst _ ((@Patterns.CPatterns (expr typ func) patterns_even) ::
                       (@Patterns.CApp (expr typ func) (@ExprCore.App typ func)) ::
                       (@Patterns.CAbs (expr typ func) reify_simple_typ (@ExprCore.Abs typ func)) ::
                       (@Patterns.CVar (expr typ func) (@ExprCore.Var typ func)) :: nil)).



Reify Pattern patterns_even += (@RExact _ Even) => (Inj (typ:=typ) 1%positive).
Reify Pattern patterns_even += (@RExact _ O) => (Inj (typ:=typ) 2%positive).
Reify Pattern patterns_even += (@RExact _ S) => (Inj (typ:=typ) 3%positive).
Reify Pattern patterns_even += (@RExact _ plus) => (Inj (typ:=typ) 4%positive).
Reify Pattern patterns_even += (@RExact _ minus) => (Inj (typ:=typ) 5%positive).

Fixpoint makeNat (n : nat) : expr typ func :=
  match n with
    | O => Inj (2)
    | S n => App (Inj 3) (makeNat n)
  end%positive.

Let RSym_func : @RSym typ _ func := SymEnv.RSym_func fs.
Local Existing Instance RSym_func.

Let Expr_expr : @ExprI.Expr typ _ (expr typ func) := @Expr_expr _ _ _ _ _.
Local Existing Instance Expr_expr.

Reify BuildLemma < SimpleReify.reify_simple_typ reify_even reify_even >
      lem_0 : Even_0.

Reify BuildLemma < SimpleReify.reify_simple_typ reify_even reify_even >
      lem_SS : Even_SS.

Reify BuildLemma < SimpleReify.reify_simple_typ reify_even reify_even >
      lem_plus : Even_plus.

Reify BuildLemma < SimpleReify.reify_simple_typ reify_even reify_even >
      lem_minus : Even_minus.


Definition evenHints : Hints typ (expr typ func) :=
{| Apply := lem_SS :: lem_0 :: lem_plus :: lem_minus :: nil
 ; Extern := from_Prover (@assumptionProver _ (expr typ func) _)
 |}.

Instance ExprOk_expr : ExprI.ExprOk Expr_expr :=
  @ExprOk_expr _ _ _ _ _ _ _ _.

Theorem evenHintsOk : @HintsOk _ _ RType_typ _ _ evenHints.
Proof.
  constructor.
  { unfold evenHints; simpl.
    repeat first [ apply Forall_cons | apply Forall_nil ].
    exact Even_SS.
    exact Even_0.
    exact Even_plus.
    exact Even_minus. }
  { unfold evenHints; simpl.
    eapply from_ProverT_correct; eauto with typeclass_instances.
    apply (@assumptionProver_correct typ _ (expr typ func) _ _ _ _ _). }
Defined.


Let subst := FMapSubst.SUBST.raw (expr typ func).
Local Instance Subst_subst : SubstI.Subst subst (expr typ func) :=
  FMapSubst.SUBST.Subst_subst _.
Local Instance SubstUpdate_subst : SubstI.SubstUpdate subst (expr typ func) :=
  @FMapSubst.SUBST.SubstUpdate_subst _ _ _ _.

Local Instance SubstOk_fmap_subst : SubstI.SubstOk subst typ (expr typ func) :=
  @FMapSubst.SUBST.SubstOk_subst _ _ _ _.
Local Instance SubstUpdateOk_fmap_subst : SubstI.SubstUpdateOk subst typ (expr typ func).
eapply (@FMapSubst.SUBST.SubstUpdateOk_subst _ _ _ _ _).
Qed.

Definition the_auto hints :=
  @auto_prove typ (expr typ func) _ _ _ _ subst _ (SUBST.SubstOpen_subst _)
                hints
                (fun tus tvs under el er (t : typ) (sub : subst) =>
                   @ExprUnify_simul.exprUnify _ _ _ _ _ _ _ _ 10 tus tvs under el er t sub).

Existing Instance SUBST.SubstOpen_subst.
Existing Instance SUBST.SubstOpenOk_subst.
Arguments ExprUnify_simul.exprUnify_sound {_ _ _ _ _ _ _ _ _ _ _ _ _} _%nat _ _ _ _ _ _ _ _ _ _.

(* TODO(gmalecha): Why is there not a lemma that says this already? *)
Theorem Apply_auto_prove (fuel : nat) hints (Hok : HintsOk hints)
: forall facts (us vs : EnvI.env) goal s',
    @the_auto hints fuel facts
              (EnvI.typeof_env us) (EnvI.typeof_env vs) goal
              (SUBST.raw_empty _) = Some s' ->
    (let (tus,us) := EnvI.split_env us in
     let (tvs,vs) := EnvI.split_env vs in
     match factsD (ExternOk Hok) tus tvs facts
         , @SubstI.substD _ _ _ _ _ _ _ tus tvs s' with
       | Some fD , Some P => fD us vs /\ P us vs
       | None , _
       | _ , None => False
     end) ->
    match @ExprI.exprD _ RType_typ _ _ us vs goal tyProp return Prop with
      | None => True
      | Some P => P
    end.
Proof.
  intros.
  generalize (@auto_prove_sound
                typ (expr typ func) _ _ _ _ _ _ _ _ Subst_subst _ _ _ _ _ hints Hok
                (ExprUnify_simul.exprUnify 10)
                (ExprUnify_simul.exprUnify_sound _) fuel).
  intro XXX; eapply XXX in H; clear XXX.
  Arguments SUBST.WellFormed_empty {_ _ _ _} _ _ _ _ _ _.
  destruct (H SUBST.WellFormed_empty); clear H.
  unfold ExprI.exprD. simpl.
  do 2 rewrite split_env_eta in *.
  edestruct (SUBST.substD_empty (expr:=expr typ func)) as [ ? [ ? ? ] ].
  erewrite H in H2.
  unfold ExprDAs.exprD'_typ0 in *. simpl in *.
  forward.
  specialize (H5 _ _ _ H0 eq_refl eq_refl); clear H0.
  destruct H5 as [ ? [ ? ? ] ].
  inv_all; subst.
  destruct H6; eapply H5; eauto.
Qed.

Definition fuel := 103.

Definition seven : expr typ func -> expr typ func :=
  App (Inj 1%positive).
Definition splus (l r : expr typ func) : expr typ func := App (App (Inj 4%positive) l) r.

Ltac run_auto := idtac;
  let rec reify X :=
      match X with
      | ?A + ?B =>
        let A := reify A in
        let B := reify B in
        uconstr:(splus A B)
      | _ => uconstr:(makeNat X)
      end
  in
  match goal with
    | |- Even ?X =>
      let rX := reify X in
      let G := constr:(App (Inj 1%positive) rX) in
      pose (g := G) ;
      let result :=
          constr:(the_auto evenHints fuel nil nil nil g (@SUBST.raw_empty (expr typ func)))
      in
      let resultV := eval vm_compute in result in
      match resultV with
        | None => fail
        | Some ?sV =>
          pose (s := sV) ;
          cut (let (tus,us) := EnvI.split_env nil in
               let (tvs,vs) := EnvI.split_env nil in
               match factsD (ExternOk evenHintsOk) tus tvs nil
                   , @SubstI.substD _ _ _ _ _ _ _ tus tvs s with
                 | Some fD , Some P => fD us vs /\ P us vs
                 | None , _
                 | _ , None => False
               end) ;
            [ cut (result = resultV) ;
              [ set (pf := @Apply_auto_prove fuel _ evenHintsOk nil nil nil g s) ;
                exact pf
              | vm_cast_no_check (@eq_refl _ (Some s))]
            | compute; split; constructor ]
      end
  end.


Goal Even 4.
Proof.
  Time run_auto.
Qed.

Goal Even 200.
Proof.
  Time run_auto.
Qed.

Goal Even 200.
Proof.
  Time eauto 700 using Even_0, Even_SS.
Qed.

Goal Even (10 + 10).
Proof.
  Time run_auto.
Qed.

Goal Even 200.
Proof.
  Time run_auto.
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

Goal Even (0 + 0).
Proof.
  run_auto.
Qed.

Goal Even ((200 + 200) + 200).
Proof.
  Time run_auto.
Qed.
