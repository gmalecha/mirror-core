Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.RTac.Interface.
Require Import MirrorCore.Lambda.Rtac.
Require MirrorCore.Subst.FMapSubst.
Require Import McExamples.Simple.Simple.

Local Instance Expr_expr : Expr _ (expr typ func) := @Expr_expr _ _ _ _ _.
Definition subst :=
  FMapSubst.SUBST.raw (expr typ func).
Local Instance Subst_subst : SubstI.Subst subst (expr typ func)
  := FMapSubst.SUBST.Subst_subst _.
Local Instance SubstUpdate_subst : SubstI.SubstUpdate subst (expr typ func)
  := @FMapSubst.SUBST.SubstUpdate_subst _ _ _ _.

Definition ptrn_all : ptrn func typ :=
  fun x _T good bad =>
    match x with
    | All t => good t
    | _ => bad x
    end.
Instance ptrn_ok_ptrn_all : ptrn_ok ptrn_all.
Proof.
  red. destruct x;
         try solve [ right; compute; reflexivity
                   | left; eexists; compute; reflexivity ].
Qed.

Instance SucceedsE_ptrn_all f t : SucceedsE f ptrn_all t :=
{ s_result := f = All t }.
Proof.
abstract (
  destruct f;
    try solve [ intro H ; exact (@H _ (fun x => All x) (fun x => x)) ]).
Defined.

Definition ptrn_impl : ptrn func unit :=
  fun x _T good bad =>
    match x with
    | Impl => good tt
    | _ => bad x
    end.
Instance ptrn_ok_ptrn_impl : ptrn_ok ptrn_impl.
Proof.
  red. destruct x;
         try solve [ right; compute; reflexivity
                   | left; eexists; compute; reflexivity ].
Qed.

Instance SucceedsE_ptrn_impl f t : SucceedsE f ptrn_impl t :=
{ s_result := f = Impl }.
Proof.
abstract (
  destruct f;
    try solve [ intro H ; exact (@H _ (fun x => Impl) (fun x => x)) ]).
Defined.

Definition open
: Ptrns.ptrn (expr typ func) (SimpleOpen typ func) :=
  por (pmap (fun xy => sAsAl (fst xy) (snd xy))
            (app (inj ptrn_all) get))
      (pmap (fun xy => let '((_,x),y) := xy in sAsHy x y)
            (app (app (inj ptrn_impl) get) get)).

Instance ptrn_ok_open : ptrn_ok open.
Proof.
  repeat first [ eapply ptrn_ok_pmap
               | eapply ptrn_ok_por
               | eapply ptrn_ok_app
               | eapply ptrn_ok_get
               | eapply ptrn_ok_inj
               | eapply ptrn_ok_ptrn_all
               | eapply ptrn_ok_ptrn_impl ].
Qed.

Theorem open_sound : simple_open_ptrn_sound open.
Proof.
  unfold open.
  do 2 red; intros.
  eapply Succeeds_por in H; eauto with typeclass_instances; destruct H.
  { eapply Succeeds_pmap in H; eauto with typeclass_instances.
    forward_reason; subst.
    eapply Succeeds_app in H; eauto with typeclass_instances.
    forward_reason; subst.
    eapply Succeeds_inj in H0; eauto with typeclass_instances.
    eapply Succeeds_get in H1.
    forward_reason; subst.
    eapply SucceedsE_ptrn_all in H0. red in H0.
    compute in H0.
    subst. simpl.
    unfold propD, exprD_typ0. simpl.
    intros. destruct x. simpl in *.
    erewrite ExprTac.lambda_exprD_AppL in H; eauto with typeclass_instances.
    Focus 2.
    instantiate (2 := tyArr t tyProp).
    rewrite lambda_exprD_Inj; eauto with typeclass_instances.
    unfold symAs; simpl.
    destruct (typ_eq_dec t t); simpl.
    compute.
    rewrite (UIP_refl e0). reflexivity.
    clear - n; congruence.
    forward; inv_all; subst.
    eexists; split; [ reflexivity | ].
    compute in H1. subst.
    intros. compute in H0. eauto. }
  { eapply Succeeds_pmap in H.
    forward_reason; subst.
    eapply Succeeds_app in H; instantiate; eauto with typeclass_instances.
    2: eauto with typeclass_instances.
    forward_reason; subst.
    eapply Succeeds_app in H0; eauto with typeclass_instances.
    forward_reason; subst.
    eapply Succeeds_get in H1; eauto with typeclass_instances.
    eapply Succeeds_get in H2; eauto with typeclass_instances.
    eapply Succeeds_inj in H0; eauto with typeclass_instances.
    forward_reason; subst.
    eapply SucceedsE_ptrn_impl in H0.
    compute in H0. subst.
    destruct x; simpl.
    destruct p; simpl.
    unfold propD, exprD_typ0. simpl.
    intros.
    forward; inv_all; subst.
    destruct x2; try solve [ exfalso; clear - H; compute in H; inversion H ].
    destruct x; try solve [ exfalso; clear - H; compute in H; inversion H ].
    rewrite H2. rewrite H1.
    do 2 eexists. split; eauto. split; eauto.
    subst. compute.
    compute in H. inv_all. subst.
    eauto. }
Qed.

Definition INTRO : rtac typ (expr typ func) :=
  @INTRO_ptrn _ _ (pmap SimpleOpen_to_OpenAs open).

Lemma open_ptrn_sound_pmap_SimpleOpen_to_OpenAs : forall x,
      ptrn_ok x ->
  simple_open_ptrn_sound x ->
  open_ptrn_sound (pmap SimpleOpen_to_OpenAs x).
Proof.
  intros. red; intros.
  eapply Succeeds_pmap in H1.
  forward_reason.
  subst.
  eapply SimpleOpen_to_OpenAs_sound; eauto.
  eassumption.
Qed.

Theorem INTRO_sound : RtacSound INTRO.
Proof.
  eapply INTRO_ptrn_sound.
  - eauto with typeclass_instances.
  - eapply open_ptrn_sound_pmap_SimpleOpen_to_OpenAs;
      eauto using open_sound with typeclass_instances.
Qed.

Definition fAll (t : typ) (P : expr typ func) : expr typ func :=
  App (Inj (All t)) (Abs t P).

Definition fImpl (P Q : expr typ func) : expr typ func :=
  App (App (Inj Impl) P) Q.

Definition fAnd (P Q : expr typ func) : expr typ func :=
  App (App (Inj And) P) Q.

Definition tac : rtac typ (expr typ func) :=
  THEN (REPEAT 10 INTRO)
       (runOnGoals (TRY EASSUMPTION)).

Definition runRTac_empty_goal (tac : rtac typ (expr typ func))
           (goal : expr typ func)  :=
  @THENK _ _ (@runOnGoals _ _ _ _ tac) (@MINIFY _ _ _ _ _)
        _ (@TopSubst _ _ nil nil)
        (@GGoal typ (expr typ func) goal).
Arguments runRTac_empty_goal _%rtac _.

Definition simple_goal : expr typ func :=
  fAll tyProp (fImpl (Var 0) (Var 0)).

Eval compute in
    runRTac_empty_goal tac simple_goal.

Definition simple_goal2 : expr typ func :=
  fAll tyProp (fImpl (Var 0) (fAll tyProp (Var 0))).

Eval compute in runRTac_empty_goal tac simple_goal2.

Definition simple_goal3 : expr typ func :=
  fAll tyProp (fImpl (Var 0) (fAll tyProp (Var 1))).

Eval compute in runRTac_empty_goal tac simple_goal3.

Definition and_lem : Lemma.lemma typ (expr typ func) (expr typ func) :=
{| Lemma.vars := tyProp :: tyProp :: nil
 ; Lemma.premises := Var 0 :: Var 1 :: nil
 ; Lemma.concl := App (App (Inj And) (Var 0)) (Var 1)
 |}.

Let to_rtacK : rtac typ (expr typ func) -> rtacK typ (expr typ func) :=
  runOnGoals.
Arguments to_rtacK _%rtac _ _ _.

Eval compute in
    let goal :=
        fAll tyProp (fAll tyProp
                          (fImpl (Var 0)
                                 (fImpl (Var 1)
                                        (fAnd (Var 0) (Var 1)))))
    in
    runRTac_empty_goal (REPEAT 10 INTRO ;;
                        APPLY and_lem ;;
                        to_rtacK (FIRST (EASSUMPTION :: IDTAC :: nil)))
                       goal.


Eval compute in
    let goal :=
        fAll tyProp (fAll tyProp
                          (fImpl (Var 0)
                                 (fImpl (Var 1)
                                        (fAnd (Var 0) (Var 1)))))
    in
    runRTac_empty_goal (REPEAT 10 INTRO ;;
                        APPLY and_lem ;;
                        to_rtacK (FIRST [ EASSUMPTION | IDTAC ]))
                       goal.

Eval compute in
    let goal :=
        fAll tyProp (fAll tyProp
                          (fImpl (Var 0)
                                 (fImpl (Var 1)
                                        (fAnd (Var 0) (Var 1)))))
    in
    runRTac_empty_goal (REPEAT 10 INTRO ;;
                        to_rtacK (EAPPLY and_lem)) goal.

Definition random_lem : Lemma.lemma typ (expr typ func) (expr typ func) :=
{| Lemma.vars := tyProp :: tyNat :: tyBool :: tyNat :: nil
 ; Lemma.premises := Var 0 :: App (App (Inj (Eq tyBool)) (App (App (Inj Lt) (Var 1)) (Var 3))) (Var 2) :: nil
 ; Lemma.concl := Var 0
 |}.

Eval compute in
    let goal :=
        fAll tyProp (fAll tyProp
                          (fImpl (Var 0)
                                 (fImpl (Var 1)
                                        (fAnd (Var 0) (Var 1)))))
    in
    runRTac_empty_goal (REPEAT 10 INTRO ;;
                        to_rtacK (EAPPLY random_lem)) goal.
