Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.CoreK.

Section parameterized.
  Variable typ : Set.
  Variable expr : Set.

  Context {RType_typ : RType typ}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Expr_expr : Expr typ expr}.
  Context {ExprUVar_expr : ExprUVar expr}.

  Section RtacSound.
  Variable tac : rtac typ expr.

  Class RtacSound : Prop :=
    RtacSound_proof :> rtac_sound tac.

  Theorem mkRtacSound : rtac_sound tac -> RtacSound.
  Proof. exact (fun x => x). Qed.

  Hypothesis tac_sound : RtacSound.

  Definition runRtac (tus tvs : tenv typ) (goal : expr) (tac : rtac typ expr) :=
    tac _ (TopSubst _ tus tvs) goal.

  Definition env_propD us vs g : Prop :=
    let (tus,us) := split_env us in
    let (tvs,vs) := split_env vs in
    match exprD_typ0 tus tvs g return Prop with
      | None => True
      | Some P => P us vs
    end.

  Lemma sigT_eta : forall {T} {F : T -> Type} (x : sigT F),
                     x = @existT _ _ (projT1 x) (projT2 x).
  Proof. destruct x. reflexivity. Qed.

  Lemma rtac_Solved_closed_soundness
  : forall us vs g,
      runRtac (typeof_env us) (typeof_env vs) g tac = Solved (@TopSubst _ _ _ _) ->
      env_propD us vs g.
  Proof.
    intros.
    eapply tac_sound in H.
    simpl in H.
    unfold env_propD, Ctx.propD in *.
    rewrite (sigT_eta (split_env us)).
    rewrite (sigT_eta (split_env vs)).
    generalize dependent (projT2 (split_env us)).
    generalize dependent (projT2 (split_env vs)).
    rewrite (split_env_typeof_env us).
    rewrite (split_env_typeof_env vs).
    intros.
    destruct (exprD_typ0 (typeof_env us) (typeof_env vs) g); trivial.
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
    match exprD_typ0 tus tvs g return Prop with
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
    destruct (exprD_typ0 (typeof_env us) (typeof_env vs) g); trivial.
    destruct H. constructor. constructor.
    simpl in *. destruct H1.
    destruct (goalD (typeof_env us) (typeof_env vs) g'); eauto.
    { destruct H2. eapply H3; eauto. }
    { inversion H2. }
  Qed.
  End RtacSound.

  Lemma rtac_sound_let
  : forall (t1 : rtac typ expr)
           (t2 : _ -> rtac typ expr),
      RtacSound t1 ->
      (forall x, RtacSound x -> rtac_sound (t2 x)) ->
      RtacSound (let x := t1 in t2 x).
  Proof using. intros. eapply H0. eauto. Qed.

  Lemma rtac_sound_letK
  : forall (t1 : rtacK typ expr) (t2 : _ -> rtac typ expr),
      rtacK_sound t1 ->
      (forall x, rtacK_sound x -> rtac_sound (t2 x)) ->
      rtac_sound (let x := t1 in t2 x).
  Proof using. eauto. Qed.

  Lemma rtacK_sound_let
  : forall (t1 : rtac typ expr)
           (t2 : _ -> rtacK typ expr),
      rtac_sound t1 ->
      (forall x, RtacSound x -> rtacK_sound (t2 x)) ->
      rtacK_sound (let x := t1 in t2 x).
  Proof using. intros. eapply H0. eauto. Qed.

  Lemma rtacK_sound_letK
  : forall (t1 : rtacK typ expr) (t2 : _ -> rtacK typ expr),
      rtacK_sound t1 ->
      (forall x, rtacK_sound x -> rtacK_sound (t2 x)) ->
      rtacK_sound (let x := t1 in t2 x).
  Proof using. eauto. Qed.

End parameterized.

Arguments RtacSound {typ expr _ _ _} _.
