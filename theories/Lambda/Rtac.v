(** Basic Rtac tactics specialized for the lambda language.
 **)
Require Import ExtLib.Tactics.
Require Import MirrorCore.Instantiate.
Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.Util.Compat.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprUnify.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.ExprTac.
Require Import MirrorCore.RTac.RTac.

Set Implicit Arguments.
Set Strict Implicit.

Section tactics.
  Context {typ func : Type}.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Typ0_Prop : Typ0 RType_typ Prop}.
  Context {Typ2_func : Typ2 RType_typ RFun}.
  Context {Typ2Ok_func : Typ2Ok Typ2_func}.
  Context {RSym_sym : RSym func}.
  Context {RSymOk_sym : RSymOk RSym_sym}.
  Let Expr_expr : Expr typ (expr typ func) := Expr_expr.
  Local Existing Instance Expr_expr.
  Let ExprOk_expr : ExprOk Expr_expr := ExprOk_expr.
  Local Existing Instance ExprOk_expr.

  (* Apply Tactics *)
  Definition EAPPLY_depth (depth : nat)
  : Lemma.lemma typ (expr typ func) (expr typ func) ->
    rtac typ (expr typ func) :=
    EAPPLY (fun subst Ssubst SUsubst => exprUnify depth).
  Definition APPLY_depth (depth : nat)
  : Lemma.lemma typ (expr typ func) (expr typ func) ->
    rtac typ (expr typ func) :=
    APPLY (fun subst Ssubst SUsubst => exprUnify depth).

  Definition EAPPLY (l : Lemma.lemma typ (expr typ func) (expr typ func))
  : rtac typ (expr typ func) :=
    EAPPLY_depth (S (length l.(Lemma.vars))) l.

  Definition APPLY (l : Lemma.lemma typ (expr typ func) (expr typ func))
  : rtac typ (expr typ func) :=
    APPLY_depth (S (length l.(Lemma.vars))) l.

  Global Instance RtacSound_EAPPLY_depth depth l (RL : ReifiedLemma l)
  : RtacSound (EAPPLY_depth depth l).
  Proof.
    eapply EAPPLY_sound; eauto with typeclass_instances.
    intros. eapply exprUnify_sound; eauto with typeclass_instances.
  Qed.

  Global Instance RtacSound_APPLY_depth depth l (RL : ReifiedLemma l)
  : RtacSound (APPLY_depth depth l).
  Proof.
    eapply APPLY_sound; eauto with typeclass_instances.
    intros. eapply exprUnify_sound; eauto with typeclass_instances.
  Qed.

  Global Instance RtacSound_EAPPLY l (RL : ReifiedLemma l)
  : RtacSound (EAPPLY l).
  Proof.
    eapply RtacSound_EAPPLY_depth; assumption.
  Qed.

  Global Instance RtacSound_APPLY l (RL : ReifiedLemma l)
  : RtacSound (APPLY l).
  Proof.
    eapply RtacSound_APPLY_depth; assumption.
  Qed.

  (* * Apply tactics with minification *)
  Definition EAPPLY_m (l : Lemma.lemma typ (expr typ func) (expr typ func))
  : rtac typ (expr typ func) :=
    THEN (EAPPLY_depth (S (length l.(Lemma.vars))) l)
         (@MINIFY _ _ _ _ _).

  Definition APPLY_m (l : Lemma.lemma typ (expr typ func) (expr typ func))
  : rtac typ (expr typ func) :=
    THEN (APPLY_depth (S (length l.(Lemma.vars))) l)
         (@MINIFY _ _ _ _ _).

  Global Instance RtacSound_EAPPLY_m l (RL : ReifiedLemma l)
  : RtacSound (EAPPLY_m l).
  Proof.
    eapply THEN_sound.
    - eapply RtacSound_proof. eauto with typeclass_instances.
    - eapply MINIFY_sound; eauto with typeclass_instances.
  Qed.

  Global Instance RtacSound_APPLY_m l (RL : ReifiedLemma l)
  : RtacSound (APPLY_m l).
  Proof.
    eapply THEN_sound.
    - eapply RtacSound_proof. eauto with typeclass_instances.
    - eapply MINIFY_sound; eauto with typeclass_instances.
  Qed.

  (* Assumption Tactics *)
  Definition EASSUMPTION : rtac typ (expr typ func) :=
    @EASSUMPTION typ (expr typ func) _ _ _
       (fun subst S_subst SU => @exprUnify subst typ func _ _ _ S_subst SU 30).

  Global Instance RtacSound_EASSUMPTION : RtacSound EASSUMPTION.
  Proof.
    eapply Assumption.ASSUMPTION_sound; eauto.
    generalize 30.
    intros.
    eapply exprUnify_sound; eauto.
  Qed.

  Section fr_to_r.
    Variable fr : full_reducer typ func.
    Definition full_reducer_to_reducer (inst : bool)
    : reducer typ (expr typ func) :=
      if inst then
        fun _ _ ctx sub e =>
          fr nil (instantiate (fun u => subst_lookup u sub) 0 e) nil
      else
        fun _ _ ctx sub e =>
          fr nil e nil.

    Hypothesis frOk : full_reducer_ok fr.
    Theorem full_reducer_to_reducer_sound (inst : bool)
    : reducer_sound (full_reducer_to_reducer inst).
    Proof.
      red; intros.
      unfold Ctx.propD, exprD_typ0 in *.
      forwardy; inv_all; subst.
      assert (vt : var_termsP nil
                              (fun (a : HList.hlist typD (getUVars ctx))
                                   (b : HList.hlist typD (getVars ctx))
                                   (c : HList.hlist typD (getUVars ctx))
                                   (d : HList.hlist typD (getVars ctx)) =>
                                 a = c /\ b = d)).
      { constructor. tauto. }
      specialize (fun PD =>
                    @frOk (if inst then
                             instantiate (fun u => subst_lookup u s) 0 e
                           else e) nil
                          (getUVars ctx) (getVars ctx)
                          (getUVars ctx) (getVars ctx)
                          (fun a b c d => a = c /\ b = d) vt nil (typ0(F:=Prop))
                          nil PD HList.Hnil).
      clear vt.
      destruct inst.
      { destruct (@instantiate_sound_ho
                    typ (expr typ func) _ _ _
                    (getUVars ctx) (getVars ctx)
                    (fun u => subst_lookup u s) e nil
                    (typ0(F:=Prop)) y
                    (fun P => forall us vs,
                         cD P us vs))
          as [ ? [ ? ? ] ]; [ | | eassumption | ].
        { generalize (SpecLemmas.ExprTApplicative_with_extra nil _ H1).
          clear - H1.
          constructor.
          { intros.
            eapply Pure_pctxD; eauto. }
          { intros.
            generalize (H0 us vs); clear H0.
            eapply Ap_pctxD; eauto.
            generalize (H2 us vs); clear H2.
            eapply Ap_pctxD; eauto.
            eapply Pure_pctxD; eauto. } }
        { eapply sem_preserves_if_ho_ctx_lookup; eauto. }
        destruct (@frOk _ H eq_refl) as [ ? [ ? ? ] ]; clear frOk.
        simpl. change_rewrite H5.
        eexists; split; [ reflexivity | ].
        intros.
        generalize (H4 us vs).
        eapply Ap_pctxD; eauto.
        eapply Pure_pctxD; eauto.
        intros.
        specialize (H7 HList.Hnil).
        simpl in H7.
        specialize (@H6 us0 vs0 us0 vs0 (conj eq_refl eq_refl)).
        simpl in H6. rewrite H6 in H7; clear H6.
        revert H7 H9. clear.
        generalize dependent (typ0_cast(F:=Prop)).
        clear.
        generalize dependent (typD (typ0(F:=Prop))).
        clear.
        intros; subst.
        rewrite H7; assumption. }
      { destruct (@frOk _ H3 eq_refl) as [ ? [ ? ? ] ]; clear frOk.
        simpl.
        rewrite H.
        eexists; split; [ reflexivity | ].
        intros.
        eapply Pure_pctxD; eauto.
        do 3 intro.
        clear - H4. specialize (H4 us0 vs0 us0 vs0 (conj eq_refl eq_refl)).
        simpl in *.
        generalize dependent (typ0_cast (F:=Prop)).
        generalize dependent (typD (typ0 (F:=Prop))).
        clear; intros; subst. rewrite H4. assumption. }
    Qed.
  End fr_to_r.

  (* Simplification Tactics *)
  Definition SIMPL (inst : bool) (fr : full_reducer typ func)
  : rtac typ (expr typ func) :=
    SIMPLIFY (full_reducer_to_reducer fr inst).

  Global Instance RtacSound_SIMPL (inst : bool) (fr : full_reducer typ func)
         (frOk : full_reducer_ok fr)
  : RtacSound (SIMPL inst fr).
  Proof.
    unfold SIMPL.
    eapply SIMPLIFY_sound.
    eapply full_reducer_to_reducer_sound. assumption.
  Qed.

  Definition INTRO_ptrn (p : ptrn (expr typ func) (OpenAs typ (expr typ func)))
  : rtac typ (expr typ func) :=
    INTRO (run_ptrn (pmap Some p) None).

  Inductive SimpleOpen : Type :=
  | sAsEx (t : typ) (l : expr typ func)
  | sAsAl (t : typ) (l : expr typ func)
  | sAsHy (p q : expr typ func).

  Definition SimpleOpen_to_OpenAs (x : SimpleOpen)
  : OpenAs typ (expr typ func) :=
    match x with
    | sAsEx t body =>
      AsEx t (fun arg => Red.beta (App body arg))
    | sAsAl t body =>
      AsAl t (fun arg => Red.beta (App body arg))
    | sAsHy p q => AsHy p q
    end.

  Definition open_ptrn_sound
             (p : ptrn (expr typ func) (OpenAs typ (expr typ func)))
  :=
    forall (tus tvs : list typ) (e : expr typ func)
           (ot : OpenAs typ (expr typ func)),
      Succeeds e p ot ->
      open_spec tus tvs e ot.

  Definition simple_open_spec (tus tvs : list typ) (e : expr typ func)
             (ot : SimpleOpen) : Prop :=
    match ot with
    | sAsEx t gl' =>
      forall (eD : exprT tus tvs Prop),
        Ctx.propD tus tvs e = Some eD ->
        exists gD' : exprT tus tvs (typD (typ2 t (typ0 (F:=Prop)))),
          exprD tus tvs (typ2 (F:=RFun) t (typ0 (F:=Prop))) gl' = Some gD' /\
          (forall (us : HList.hlist typD tus) (vs : HList.hlist typD tvs),
              (exists x : typD t,
                  castD (fun x => x) (typD t -> Prop) (Typ0:=Typ0_Arr _ (Typ0_term _ t) _) (gD' us vs) x) -> eD us vs)
    | sAsAl t gl' =>
      forall (eD : exprT tus tvs Prop),
        Ctx.propD tus tvs e = Some eD ->
        exists gD' : exprT tus tvs (typD (typ2 t (typ0 (F:=Prop)))),
          exprD tus tvs (typ2 (F:=RFun) t (typ0 (F:=Prop))) gl' = Some gD' /\
          (forall (us : HList.hlist typD tus) (vs : HList.hlist typD tvs),
              (forall x : typD t,
                  castD (fun x => x) (typD t -> Prop) (Typ0:=Typ0_Arr _ (Typ0_term _ t) _) (gD' us vs) x) -> eD us vs)
    | sAsHy h gl' =>
      forall eD : exprT tus tvs Prop,
        Ctx.propD tus tvs e = Some eD ->
        exists eD' hD : exprT tus tvs Prop,
          Ctx.propD tus tvs h = Some hD /\
          Ctx.propD tus tvs gl' = Some eD' /\
          (forall (us : HList.hlist typD tus) (vs : HList.hlist typD tvs),
              (hD us vs -> eD' us vs) -> eD us vs)
    end.

  Definition simple_open_ptrn_sound (p : ptrn (expr typ func) SimpleOpen) : Prop :=
    forall tus tvs e ot,
      Succeeds e p ot ->
      simple_open_spec tus tvs e ot.

  Local Opaque Red.beta.

  Definition INSTANTIATE : rtac typ (expr typ func) := INSTANTIATE.

  Instance RtacSound_INSTANTIATE : RtacSound INSTANTIATE.
  Proof. eapply mkRtacSound.
         eapply INSTANTIATE_sound.
  Qed.

  (** TODO(gmalecha): These exist elsewhere. *)
  Lemma exprD_AppL : forall tus tvs tx ty f x fD,
      lambda_exprD tus tvs (typ2 (F:=RFun) tx ty) f = Some fD ->
      lambda_exprD tus tvs ty (App f x) =
      match exprD tus tvs tx x with
      | None => None
      | Some xD => Some (AbsAppI.exprT_App fD xD)
      end.
  Proof.
    simpl; intros.
    rewrite lambda_exprD_App.
    destruct (ExprDsimul.ExprDenote.lambda_exprD tus tvs tx x) eqn:?.
    { erewrite ExprTac.lambda_exprD_typeof_Some by eassumption.
      rewrite H. rewrite Heqo. reflexivity. }
    { destruct (typeof_expr tus tvs x) eqn:?; auto.
      destruct (ExprDsimul.ExprDenote.lambda_exprD tus tvs (typ2 t ty) f) eqn:?; auto.
      assert (t = tx).
      { destruct (ExprFacts.lambda_exprD_single_type H Heqo1).
        clear H0. eapply typ2_inj in x0; eauto.
        destruct x0. symmetry. apply H0. }
      { subst. rewrite Heqo. reflexivity. } }
  Qed.

  (** TODO(gmalecha): These exist elsewhere. *)
  Lemma exprD_AppR : forall tus tvs tx ty f x xD,
      lambda_exprD tus tvs tx x = Some xD ->
      lambda_exprD tus tvs ty (App f x) =
      match lambda_exprD tus tvs (typ2 tx ty) f with
      | None => None
      | Some fD => Some (AbsAppI.exprT_App fD xD)
      end.
  Proof.
    simpl; intros.
    rewrite lambda_exprD_App.
    erewrite ExprTac.lambda_exprD_typeof_Some by eassumption.
    rewrite H.
    reflexivity.
  Qed.

  (** TODO(gmalecha): These exist elsewhere. *)
  Lemma exprD_App_both_cases : forall tus tvs tx ty f x fD xD,
      lambda_exprD tus tvs (typ2 (F:=RFun) tx ty) f = Some fD ->
      lambda_exprD tus tvs tx x = Some xD ->
      lambda_exprD tus tvs ty (App f x) = Some (AbsAppI.exprT_App fD xD).
  Proof.
    intros. erewrite exprD_AppR by eassumption.
    rewrite H. reflexivity.
  Qed.

  Theorem SimpleOpen_to_OpenAs_sound : forall tus tvs e ot,
      simple_open_spec tus tvs e ot ->
      open_spec tus tvs e (SimpleOpen_to_OpenAs ot).
  Proof.
    destruct ot; eauto.
    + unfold simple_open_spec, open_spec.
      simpl. intros.
      specialize (H _ H0); clear H0.
      destruct H as [ ? [ ? ? ] ].
      generalize (Red.beta_sound (tus ++ t::nil) tvs (App l e') (typ0 (F:=Prop))).
      change (ExprDsimul.ExprDenote.lambda_exprD (tus ++ t::nil) tvs (typ0 (F:=Prop)) (App l e'))
        with (lambda_exprD (tus ++ t::nil) tvs (typ0 (F:=Prop)) (App l e')).
      destruct (@exprD_weakenU typ _ (expr typ func) Expr_expr _ _ (t::nil) _ l _ x H) as [ ? [ ? ? ] ].
      erewrite lambda_exprD_App_both_cases; eauto.
      intros; forwardy.
      unfold Ctx.propD, exprD_typ0.
      change_rewrite H5.
      eexists; split; [ reflexivity | ].
      intros.
      destruct H7.
      eapply H0; clear H0.
      specialize (H6 (HList.hlist_app us (HList.Hcons x1 HList.Hnil)) vs).
      specialize (H4 us vs (HList.Hcons x1 HList.Hnil)).
      exists x1.
      revert H7.
      clear - H6 H4 H2.
      unfold castD. simpl.
      unfold AbsAppI.exprT_App in *.
      generalize dependent (typ2_cast t (typ0 (F:=Prop))).
      generalize dependent (typ0_cast (F:=Prop)).
      generalize dependent (typD (typ2 t (typ0 (F:=Prop)))).
      generalize dependent (typD (typ0 (F:=Prop))).
      intros. subst; simpl in *.
      rewrite H2 in *.
      rewrite H4; clear H4.
      rewrite H6; clear H6.
      assumption.
    + intros. red. red in H.
      simpl in *. intros.
      specialize (H _ H0). destruct H as [ ? [ ? ? ] ].
      generalize (Red.beta_sound tus (tvs ++ t::nil) (App l e') (typ0 (F:=Prop))).
      change (ExprDsimul.ExprDenote.lambda_exprD tus (tvs ++ t::nil) (typ0 (F:=Prop)) (App l e'))
      with (lambda_exprD tus (tvs ++ t::nil) (typ0 (F:=Prop)) (App l e')).
      destruct (@exprD_weakenV typ _ (expr typ func) Expr_expr _ tus tvs (t::nil) _ _ _ H) as [ ? [ ? ? ] ].
      erewrite lambda_exprD_App_both_cases; eauto.
      intros; forwardy.
      unfold Ctx.propD, exprD_typ0.
      change_rewrite H6.
      eexists; split; [ reflexivity | ].
      intros.
      eapply H3; clear H3.
      intros.
      specialize (H8 x1).
      clear - H8 H2 H5 H7.
      specialize (H7 us (HList.hlist_app vs (HList.Hcons x1 HList.Hnil))).
      specialize (H5 us vs (HList.Hcons x1 HList.Hnil)).
      unfold AbsAppI.exprT_App, castD in *. simpl in *.
      generalize dependent (typ2_cast t (typ0 (F:=Prop))).
      generalize dependent (typ0_cast (F:=Prop)).
      generalize dependent (typD (typ2 t (typ0 (F:=Prop)))).
      generalize dependent (typD (typ0 (F:=Prop))).
      intros; subst. simpl in *.
      rewrite H5; clear H5.
      rewrite H2 in *.
      rewrite H7. assumption.
  Qed.

  Definition INTRO_ptrn_sound : forall p,
      ptrn_ok p ->
      open_ptrn_sound p ->
      rtac_sound (INTRO_ptrn p).
  Proof.
    intros.
    apply INTRO_sound.
    red. intros.
    revert H1.
    eapply run_ptrn_sound.
    - eapply ptrn_ok_pmap. eassumption.
    - red. red. red. intros.
      subst. tauto.
    - intros.
      eapply Succeeds_pmap in H1; eauto.
      destruct H1 as [ ? [ ? ? ] ]; subst.
      inv_all; subst.
      red in H0.
      specialize (H0 tus tvs _ _ H1).
      eauto.
    - inversion 1.
  Qed.

End tactics.

Arguments SimpleOpen _ _ : clear implicits.