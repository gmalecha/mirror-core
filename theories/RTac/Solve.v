Require Import ExtLib.Tactics.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.IsSolved.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Context {typ : Type}.
  Context {expr : Type}.
  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {ExprUVar_expr : ExprUVar expr}.

  Definition SOLVE (tac : rtac typ expr) : rtac typ expr :=
    fun tus tvs nus nvs ctx s g =>
      match is_solved (tac tus tvs nus nvs ctx s g) with
      | Some s => Solved s
      | _ => Fail
      end.

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

  Theorem SOLVE_sound
  : forall tac, rtac_sound tac -> rtac_sound (SOLVE tac).
  Proof.
    unfold SOLVE, rtac_sound.
    intros.
    specialize (H ctx s g).
    destruct (is_solved (tac (getUVars ctx) (getVars ctx) (length (getUVars ctx))
              (length (getVars ctx)) ctx s g)) eqn:?; subst; try apply rtac_spec_Fail.
    eapply is_solved_sound in Heqo.
    eapply Proper_rtac_spec_impl.
    { reflexivity. }
    { eapply Heqo. }
    { eapply H. reflexivity. }
  Qed.

  Fixpoint SOLVES (tacs : list (rtac typ expr)) : rtac typ expr :=
    match tacs with
    | nil => fun tus tvs nus nvs ctx s g => Fail
    | tac :: tacs =>
      let rec := SOLVES tacs in
      fun tus tvs nus nvs ctx s g =>
        match is_solved (tac tus tvs nus nvs ctx s g) with
        | Some s => Solved s
        | _ => rec tus tvs nus nvs ctx s g
        end
    end.

  Theorem SOLVES_sound
  : forall tacs, Forall rtac_sound tacs -> rtac_sound (SOLVES tacs).
  Proof.
    induction 1; simpl.
    { red. intros; subst. eapply rtac_spec_Fail. }
    { red.
      intros.
      destruct (is_solved (x (getUVars ctx) (getVars ctx) (length (getUVars ctx))
                             (length (getVars ctx)) ctx s g)) eqn:?; subst; eauto.
      eapply is_solved_sound in Heqo.
      eapply Proper_rtac_spec_impl.
      { reflexivity. }
      { eapply Heqo. }
      { eapply H. reflexivity. } }
  Qed.

End parameterized.

Arguments SOLVE {_ _} _%rtac _ _ _ _ _ _ _.
Arguments SOLVES {_ _} _%or_rtac _ _ _ _ _ _ _.