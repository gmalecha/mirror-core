Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relations.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Prop.
Require Import ExtLib.Data.Pair.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.CoreK.
Require Import MirrorCore.RTac.SpecLemmas.

Require Import MirrorCore.Util.Quant.
Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section runOnGoals.
  Context {typ : Type}.
  Context {expr : Type}.

  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.

  Fixpoint all_instantiated (tes : list (typ * option expr)) : bool :=
    match tes with
      | nil => true
      | (_,None) :: _ => false
      | (_,Some _) :: tes => all_instantiated tes
    end.

  Inductive ResultAnd (c : Ctx typ expr) : Type :=
  | RAFail
  | RASolved : ctx_subst c -> list (rtac typ expr) -> ResultAnd c
  | RAMore_ : ctx_subst c -> Goal typ expr -> list (rtac typ expr) -> ResultAnd c.

  Definition ResultAnd_to_Result_and c (r : ResultAnd c)
  : Result c * list (rtac typ expr) :=
    match r with
      | RAFail => (Fail, nil)
      | RASolved s tacs => (Solved s, tacs)
      | RAMore_ s g tacs => (More_ s g, tacs)
    end.

  Arguments RAFail {_}.
  Arguments RASolved {_} _ _.
  Arguments RAMore_ {_} _ _ _.

  Fixpoint runOnGoals_list_rec
           (tacs : list (rtac typ expr)) (tus tvs : tenv typ) (nus nvs : nat)
           (ctx : Ctx typ expr) (s : ctx_subst ctx) (g : Goal typ expr)
           {struct g}
  : ResultAnd ctx :=
    match g with
      | GGoal e =>
        match tacs with
          | tac :: tacs =>
            match @tac tus tvs nus nvs ctx s e with
              | Fail => RAFail
              | Solved s' => RASolved s' tacs
              | More_ s' g' => RAMore_ s' g' tacs
            end
          | nil => RAFail
        end
      | GSolved => RASolved s tacs
      | GAll t g =>
        match
          @runOnGoals_list_rec tacs tus (tvs ++ t :: nil) nus (S nvs)
                           (CAll ctx t) (AllSubst s) g
        with
          | RAFail => RAFail
          | RASolved s' tacs' => RASolved (fromAll s') tacs'
          | RAMore_ s' g' tacs' => RAMore_ (fromAll s') (GAll t g') tacs'
        end
      | GExs ts sub g =>
        let s' := remembers s ts sub in
        match
          @runOnGoals_list_rec tacs (tus ++ ts) tvs (length ts + nus) nvs
                           (CExs ctx ts) s' g
        with
          | RAFail => RAFail
          | RASolved s'' tacs' =>
            let '(shere,cs') := fromExs s'' in
            (** Here I can drop anything that is already instantiated. **)
            if amap_is_full (length ts) shere then
              RASolved cs' tacs'
            else
              (** TODO(gmalecha): I can be more aggressive here *)
              RAMore_ cs' (GExs ts shere GSolved) tacs'
          | RAMore_ s'' g' tacs' =>
            let '(shere,cs') := fromExs s'' in
            (** TODO(gmalecha)
             ** Here I need to drop already instantiated vars and
             ** substitute through. Ideally, I should collapse as much
             ** as possible.
             **)
            RAMore_ cs' (GExs ts shere g') tacs'
        end
      | GHyp h g =>
        match
          @runOnGoals_list_rec tacs tus tvs nus nvs (CHyp ctx h) (HypSubst s) g
        with
          | RAFail => RAFail
          | RASolved s' tacs' => RASolved (fromHyp s') tacs'
          | RAMore_ s' g' tacs' => RAMore_ (fromHyp s') (GHyp h g') tacs'
        end
      | GConj_ l r =>
        (** NOTE: It would be nice if I could eagerly
         ** instantiate [r] with any results that came
         ** from [l].
         **)
        match
          @runOnGoals_list_rec tacs tus tvs nus nvs ctx s l
        with
          | RAFail => RAFail
          | RASolved s' tacs' =>
            runOnGoals_list_rec tacs' tus tvs nus nvs s' r
          | RAMore_ s' g' tacs' =>
            match
              runOnGoals_list_rec tacs' tus tvs nus nvs s' r
            with
              | RAFail => RAFail
              | RASolved s'' tacs'' =>
                RAMore_ s'' g' tacs''
              | RAMore_ s'' g'' tacs'' =>
                RAMore_ s'' (GConj_ g' g'') tacs''
            end
        end
    end.

  Definition runOnGoals_list (tacs : list (rtac typ expr)) : rtacK typ expr :=
    fun tus tvs nus nvs ctx sub g =>
      (* This follows ltac semantics and requires the right number of goals *)
      match @runOnGoals_list_rec tacs tus tvs nus nvs ctx sub g with
        | RAMore_ sub' g' nil => More_ sub' g'
        | RASolved sub' nil => Solved sub'
        | _ => Fail
      end.

  Lemma runOnGoals_list_rec_sound_ind
  : forall g tacs ctx s ra,
      Forall rtac_sound tacs ->
      (@runOnGoals_list_rec tacs
                              (getUVars ctx)
                              (getVars ctx)
                              (countUVars ctx)
                              (countVars ctx)
                              ctx s g) = ra ->
      forall r tacs',
      ResultAnd_to_Result_and ra = (r,tacs') ->
      @rtac_spec typ expr _ _ _ ctx s g r /\
      Forall rtac_sound tacs'.
  Proof.
    induction g.
    { (* All *)
      intros. simpl in H0.
      match goal with
        | _ : context [ match ?X with _ => _ end ] |- _ =>
          consider X
      end; intros.
      { subst. simpl in *. inv_all. subst. split; constructor. }
      { subst. simpl in *. inv_all; subst.
        simpl in *.
        specialize (@IHg tacs (CAll ctx t) (AllSubst s) _ H H0 _ _ eq_refl).
        destruct IHg; split; auto.
        intros. inv_all.
        destruct (eta_ctx_subst_all c); subst.
        simpl in *.
        assert (WellFormed_ctx_subst (AllSubst (t:=t) s)).
        { constructor. auto. }
        specialize (H1 H3 H5); clear H5.
        forward_reason.
        inv_all.
        split; auto.
        forward. destruct H8. inv_all; subst.
        split; auto. }
      { subst. simpl in *. inv_all; subst.
        simpl in *.
        specialize (@IHg tacs (CAll ctx t) (AllSubst s) _ H H0 _ _ eq_refl).
        destruct IHg; split; auto.
        intros. inv_all.
        destruct (eta_ctx_subst_all c); subst.
        simpl in *.
        assert (WellFormed_ctx_subst (AllSubst (t:=t) s)).
        { constructor. auto. }
        specialize (H1 H3 H5); clear H5.
        forward_reason.
        inv_all.
        split; auto.
        split; auto.
        { constructor; auto. }
        forward. destruct H10. inv_all; subst.
        split; eauto.
        intros. gather_facts.
        eapply Pure_pctxD; eauto. } }
    { (* Exs *)
      simpl; intros.
      specialize (IHg tacs (CExs ctx l) (remembers s l a)).
      simpl in IHg.
      destruct (runOnGoals_list_rec
                  tacs (getUVars ctx ++ l)
                  (getVars ctx) (length l + countUVars ctx)
                  (countVars ctx) (remembers s l a) g);
        specialize (IHg _ H eq_refl _ _ eq_refl); subst;
        inversion H1; clear H1; subst.
      { split; constructor. }
      { rewrite (ctx_subst_eta c) in H2. simpl in H2.
        consider (amap_is_full (length l) (fst (fromExs c))).
        { intros. inversion H1; clear H1; subst.
          destruct IHg. split; auto.
          clear H H2.
          revert H1. revert H0.
          intros.
          eapply rtac_spec_remembers_full_Solved; eauto.
          unfold amap_is_full.
          eapply rel_dec_eq_true; eauto with typeclass_instances. }
        { intro XXX; clear XXX.
          simpl. intro XXX; inversion XXX; clear XXX; subst.
          destruct IHg; split; auto.
          clear H H1.
          eapply rtac_spec_Exs_More.
          eapply Proper_rtac_spec.
          3: eassumption.
          reflexivity.
          symmetry. change (Solved c) with (More c GSolved).
          eapply More_More_. reflexivity. } }
      { rewrite (ctx_subst_eta c) in H2. simpl in H2.
        inv_all. subst.
        destruct IHg. split; eauto using rtac_spec_Exs_More. } }
    { (* Hyp *)
      simpl. intros.
      specialize (IHg tacs (CHyp ctx e) (HypSubst s)).
      simpl in IHg.
      destruct (runOnGoals_list_rec
                  tacs (getUVars ctx) (getVars ctx)
                  (countUVars ctx) (countVars ctx) (HypSubst s) g);
        specialize (IHg _ H eq_refl _ _ eq_refl).
      { subst; inversion H1; clear H1; subst.
        simpl. split; constructor. }
      { subst; inversion H1; clear H1; subst.
        destruct IHg; split; auto.
        revert H0.
        eapply rtac_spec_Hyp_Solved. }
      { destruct IHg.
        subst. inversion H1; clear H1; subst.
        split; auto.
        eapply rtac_spec_Hyp_More. auto. } }
    { simpl; intros.
      specialize (IHg1 tacs ctx s).
      destruct (runOnGoals_list_rec
                  tacs (getUVars ctx) (getVars ctx)
                  (countUVars ctx) (countVars ctx) s g1);
        specialize (IHg1 _ H eq_refl _ _ eq_refl); subst.
      { inversion H1; clear H1; subst.
        simpl; split; constructor. }
      { specialize (IHg2 l ctx c).
        destruct IHg1.
        destruct (runOnGoals_list_rec
                    l (getUVars ctx) (getVars ctx)
                    (countUVars ctx) (countVars ctx) c g2);
          specialize (IHg2 _ H2 eq_refl _ _ eq_refl).
        { inversion H1; clear H1; subst.
          split; constructor. }
        { inversion H1; clear H1; subst.
          forward_reason; split; eauto using rtac_spec_Conj_Solved. }
        { inversion H1; clear H1; subst.
          forward_reason; split; eauto using rtac_spec_Conj_Solved. } }
      { specialize (IHg2 l ctx c).
        destruct IHg1.
        destruct (runOnGoals_list_rec
                    l (getUVars ctx) (getVars ctx)
                    (countUVars ctx) (countVars ctx) c g2);
          destruct (IHg2 _ H2 eq_refl _ _ eq_refl); clear IHg2;
          inversion H1; clear H1; subst.
        { split; constructor. }
        { split; auto.
          eapply rtac_spec_GConj_More_Solved; eauto. }
        { split; auto.
          eapply rtac_spec_GConj_More_More; eauto. } } }
    { (* Goal *)
      simpl. destruct 1; intros; subst.
      { inversion H0; clear H0; subst.
        split; constructor. }
      { specialize (H ctx s e).
        simpl in H.
        rewrite countVars_getVars in H2.
        rewrite countUVars_getUVars in H2.
        destruct (x (getUVars ctx) (getVars ctx) (length (getUVars ctx))
                    (length (getVars ctx)) ctx s e);
          specialize (H _ eq_refl); inversion H2; clear H2; subst; eauto. } }
    { (* Solved *)
      simpl. intros; subst.
      inversion H1; clear H1; subst.
      split; auto.
      eapply rtac_spec_GSolved_Solved. }
  Qed.

End runOnGoals.

Arguments runOnGoals_list {typ expr RType Expr} tac tus tvs nus nvs ctx csub goal : rename.

Section runOnGoals_list_proof.
  Context {typ : Type}.
  Context {expr : Type}.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.

  Definition ON_EACH : list (rtac typ expr) -> rtacK typ expr := runOnGoals_list.

  Theorem runOnGoals_list_sound
  : forall tacs,
      Forall rtac_sound tacs -> rtacK_sound (runOnGoals_list tacs).
  Proof.
    intros. red. intros.
    generalize (@runOnGoals_list_rec_sound_ind typ expr _ _ _ _ _ g tacs ctx s).
    unfold runOnGoals_list in H0.
    rewrite countUVars_getUVars in *.
    rewrite countVars_getVars in *.
    destruct (runOnGoals_list_rec
                tacs (getUVars ctx) (getVars ctx)
                (length (getUVars ctx)) (length (getVars ctx)) s g); subst;
    intro XXX; specialize (XXX _ H eq_refl _ _ eq_refl).
    { tauto. }
    { destruct l. tauto. constructor. }
    { destruct l. tauto. constructor. }
  Qed.

  Definition ON_EACH_sound
  : forall tacs, Forall rtac_sound tacs -> rtacK_sound (ON_EACH tacs)
  := runOnGoals_list_sound.
End runOnGoals_list_proof.
