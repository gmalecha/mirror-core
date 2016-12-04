Require Import ExtLib.Tactics.
Require Import MirrorCore.RTac.Core.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Context {typ : Set}.
  Context {expr : Set}.
  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr typ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {ExprUVar_expr : ExprUVar expr}.

  (** TODO(gmalecha): This is not complete! *)
  Fixpoint is_solved_goal (g : Goal typ expr) : bool :=
    match g with
    | GSolved => true
    | GHyp _ g'
    | GAll _ g' => is_solved_goal g'
(*    | GExs ts sub g => if amap_is_full (length ts) sub then is_solved_goal g else false *)
    | GConj_ l r => if is_solved_goal l then is_solved_goal r else false
    | _ => false
    end.
  Definition is_solved {c} (r : @Result typ expr c) : option (ctx_subst c) :=
    match r with
    | Solved s => Some s
    | More_ s g => if is_solved_goal g then Some s else None
    | Fail => None
    end.

  Theorem is_solved_goal_sound
  : forall g, @is_solved_goal g = true ->
              forall c (cs : ctx_subst c),
                GoalImplies (cs, g) (cs, GSolved).
  Proof.
    induction g; simpl; try congruence; intros;
    repeat (split; [ solve [ auto | constructor ] | ]).
    { specialize (IHg H (CAll c t) (AllSubst cs)).
      inv_all. eapply IHg in H0.
      destruct H0.
      - constructor; auto.
      - destruct H2.
        simpl in *. forward.
        destruct H5; inv_all. subst.
        split; auto.
        intros.
        gather_facts.
        eapply Pure_pctxD; eauto. }
    { specialize (IHg H (CHyp c e) (HypSubst cs)); clear H.
      inv_all. destruct IHg as [ ? [ ? ? ] ]; eauto.
      - constructor; auto.
      - simpl in *. forward.
        split; [ reflexivity | ].
        destruct H6.
        intros.
        gather_facts.
        eapply Pure_pctxD; eauto. intros.
        simpl. eauto. }
    { destruct (is_solved_goal g1); try congruence.
      specialize (IHg1 eq_refl _ cs).
      specialize (IHg2 H _ cs); clear H.
      inv_all.
      destruct IHg1 as [ ? [ ? ? ] ]; eauto.
      destruct IHg2 as [ ? [ ? ? ] ]; eauto.
      simpl in *.
      forward.
      forward_reason.
      split; auto.
      intros. gather_facts.
      eapply Pure_pctxD; eauto. }
    { forward. split.
      reflexivity.
      intros. eapply Pure_pctxD; eauto. }
  Qed.

  Definition ImplResult (c : Ctx typ expr) (r1 r2 : Result c) : Prop :=
    Option.Roption (GoalImplies (ctx:=c))
                   (fromResult r1) (fromResult r2).

  Instance Reflexive_ImplResult {c} : Reflexive (@ImplResult c).
  Proof.
    red. red. intros.
    apply Option.Reflexive_Roption.
    eapply Reflexive_GoalImplies.
  Qed.

  Theorem is_solved_sound
  : forall c r s', @is_solved c r = Some s' ->
                   ImplResult r (Solved s').
  Proof.
    destruct r; simpl.
    { inversion 1. }
    { intros.
      generalize (@is_solved_goal_sound g).
      destruct (is_solved_goal g); try congruence.
      intro. specialize (H0 eq_refl).
      inv_all. subst.
      red. simpl. constructor.
      eauto. }
    { inversion 1. reflexivity. }
  Qed.

  Lemma Proper_rtac_spec_impl : forall
      (ctx : Ctx typ expr) (s : ctx_subst ctx),
      Morphisms.Proper
        (Morphisms.respectful (fun x y => GoalImplies (s,x) (s,y))
                              (Morphisms.respectful (Basics.flip (ImplResult (c:=ctx))) (Basics.flip Basics.impl))) 
        (rtac_spec s).
  Proof.
    do 3 red. simpl.
    intros.
    red. intro.
    eapply rtac_spec_rtac_spec_modular; try reflexivity.
    eapply rtac_spec_rtac_spec_modular in H1; try reflexivity.
    unfold rtac_spec_modular in *. revert H1.
    inversion H0; clear H0; auto.
    simpl.
    clear H1 H2.
    destruct x1; destruct y1; simpl in *.
    intros; forward_reason.
    split; auto.
    split; auto.
    forward. forward_reason.
    split.
    { etransitivity; eauto. }
    { intros.
      repeat progress (gather_facts;
                       eapply pctxD_SubstMorphism; [ | | eassumption | ]; eauto).
      eapply Pure_pctxD; eauto. }
  Qed.

End parameterized.
