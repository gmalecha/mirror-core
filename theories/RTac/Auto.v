Require Import ExtLib.Data.List.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.UnifyI.
Require Import MirrorCore.RTac.EApply.
Require Import MirrorCore.RTac.Assumption.
Require Import MirrorCore.RTac.Rec.
Require Import MirrorCore.RTac.First.
Require Import MirrorCore.RTac.Fail.
Require Import MirrorCore.RTac.Then.
Require Import MirrorCore.RTac.Assumption.
Require Import MirrorCore.RTac.RunOnGoals.

Set Implicit Arguments.
Set Strict Implicit.


Section with_list.
  Context {T} (P : T -> Prop) .

  Lemma Forall_app_iff : forall ls ls', Forall P (ls ++ ls') <-> (Forall P ls /\ Forall P ls').
  Proof.
    induction ls.
    - constructor; auto. destruct 1; auto.
    - simpl; intros. do 2 rewrite Forall_cons_iff. rewrite IHls. tauto.
  Qed.

  Lemma Forall_rev : forall ls, Forall P ls -> Forall P (rev ls).
  Proof using.
    clear.
    induction 1.
    - constructor.
    - simpl. rewrite Forall_app_iff. rewrite Forall_cons_iff. auto.
  Qed.
End with_list.


Section parameterized.
  Variable typ : Type.
  Variable expr : Type.

  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Expr_expr : Expr typ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.
  Context {ExprUVar_expr : ExprUVar expr}.
  Context {ExprUVarOk_expr : ExprUVarOk _}.

  Variable exprUnify : forall subst, Subst subst expr -> SubstUpdate subst expr ->
    unifier typ expr subst.

  Variable exprUnify_sound
  : forall subst (S : Subst subst expr) (SO : SubstOk subst typ expr) SU
           (SUO : SubstUpdateOk subst typ expr),
      unify_sound (@exprUnify subst S SU).

  Record Hints : Type := mkHints
  { Extern : list (rtac typ expr -> rtac typ expr)
  ; Lemmas : list (Lemma.lemma typ expr expr) }.

  Definition EAUTO (n : nat) (h : Hints) : rtac typ expr :=
    let lems := List.rev h.(Lemmas) in
    let ext  := List.rev h.(Extern) in
    REC n
        (fun rec =>
           FIRST (EASSUMPTION exprUnify ::
           (fix each es :=
              match es with
              | nil => (fix each ls :=
                          match ls with
                          | nil => FAIL
                          | l :: ls => FIRST (THEN (EAPPLY exprUnify l) (ON_ALL rec) :: each ls :: nil)
                          end) lems
              | e :: es => FIRST (e rec :: each es :: nil)
              end) ext :: nil)
           )
        FAIL.

  Definition HintOk (h : Hints) : Prop :=
    Forall (fun r => forall rec, rtac_sound rec -> rtac_sound (r rec)) h.(Extern) /\
    Forall (@ReifiedLemma typ expr _ _ _) h.(Lemmas).

  Theorem EAUTO_sound : forall n h, HintOk h -> rtac_sound (EAUTO n h).
  Proof.
    generalize (EAPPLY_sound exprUnify exprUnify_sound).
    unfold EAUTO. intros.
    eapply REC_sound; [ | eapply FAIL_sound ].
    intros.
    destruct H0.
    eapply Forall_rev in H0.
    eapply Forall_rev in H2.
    eapply FIRST_sound; constructor; [ eapply ASSUMPTION_sound; eauto | constructor ; [ | constructor ] ].
    induction H0.
    { induction H2.
      - eapply FAIL_sound.
      - eapply FIRST_sound. constructor.
        + eapply THEN_sound. eapply EAPPLY_sound; eauto.
          eapply ON_ALL_sound. eauto.
        + constructor; [ eassumption | constructor ]. }
    { eapply FIRST_sound; constructor; [ eauto | constructor; [ eauto | constructor ] ]. }
  Qed.

End parameterized.

Hint Opaque EAUTO : typeclass_instances.
Typeclasses Opaque EAUTO.

Arguments EAUTO {typ expr _ _ _ _} unify hints depth _ _ _ : rename.