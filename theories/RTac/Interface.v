Require Import MirrorCore.RTac.Core.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.

  Context {RType_typ : RType typ}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {ExprUVar_expr : ExprUVar expr}.

  Variable tac : rtac typ expr.

  Class RtacSound : Prop :=
  { RtacSound_proof : rtac_sound tac }.

  Hypothesis tac_sound : rtac_sound tac.

  Definition runRtac (tus tvs : tenv typ) (goal : expr) (tac : rtac typ expr) :=
    tac tus tvs (length tus) (length tvs) _ (TopSubst _ tus tvs) goal.


  Definition propD us vs g : Prop :=
    let (tus,us) := split_env us in
    let (tvs,vs) := split_env vs in
    match exprD'_typ0 tus tvs g return Prop with
      | None => True
      | Some P => P us vs
    end.

  Lemma sigT_eta : forall {T} {F : T -> Type} (x : sigT F),
                     x = @existT _ _ (projT1 x) (projT2 x).
  Proof. destruct x. reflexivity. Qed.

  Lemma rtac_Solved_closed_soundness
  : forall us vs g,
      runRtac (typeof_env us) (typeof_env vs) g tac = Solved (@TopSubst _ _ _ _) ->
      propD us vs g.
  Proof.
    intros.
    eapply tac_sound in H.
    simpl in H.
    unfold propD, Ctx.propD in *.
    rewrite (sigT_eta (split_env us)).
    rewrite (sigT_eta (split_env vs)).
    generalize dependent (projT2 (split_env us)).
    generalize dependent (projT2 (split_env vs)).
    rewrite (split_env_typeof_env us).
    rewrite (split_env_typeof_env vs).
    intros.
    destruct (exprD'_typ0 (typeof_env us) (typeof_env vs) g); trivial.
    destruct H. constructor. constructor.
    destruct H0.
    eapply H1.
  Qed.

  Definition closedD us vs g g' : Prop :=
    let (tus,us) := split_env us in
    let (tvs,vs) := split_env vs in
    match goalD tus tvs g' with
      | Some G => G us vs
      | _ => True
    end ->
    match exprD'_typ0 tus tvs g return Prop with
      | None => True
      | Some P => P us vs
    end.

  Lemma rtac_More_closed_soundness
  : forall us vs g g',
      runRtac (typeof_env us) (typeof_env vs) g tac = More_ (@TopSubst _ _ _ _) g' ->
      closedD us vs g g'.
  Proof.
    intros. unfold closedD.
    eapply tac_sound in H.
    simpl in H.
    unfold Ctx.propD in *.
    rewrite (sigT_eta (split_env us)).
    rewrite (sigT_eta (split_env vs)).
    generalize dependent (projT2 (split_env us)).
    generalize dependent (projT2 (split_env vs)).
    rewrite (split_env_typeof_env us).
    rewrite (split_env_typeof_env vs).
    intros.
    destruct (exprD'_typ0 (typeof_env us) (typeof_env vs) g); trivial.
    destruct H. constructor. constructor.
    simpl in *. destruct H1.
    destruct (goalD (typeof_env us) (typeof_env vs) g'); eauto.
    { destruct H2. eapply H3; eauto. }
    { inversion H2. }
  Qed.
End parameterized.