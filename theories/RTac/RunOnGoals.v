Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relations.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Prop.
Require Import ExtLib.Data.Pair.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.HList.
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

  Variable tac : rtac typ expr.

  Fixpoint all_instantiated (tes : list (typ * option expr)) : bool :=
    match tes with
      | nil => true
      | (_,None) :: _ => false
      | (_,Some _) :: tes => all_instantiated tes
    end.

  Fixpoint runOnGoals (tus tvs : tenv typ) (nus nvs : nat)
           (ctx : Ctx typ expr) (s : ctx_subst ctx) (g : Goal typ expr)
           {struct g}
  : Result ctx :=
    match g with
      | GGoal e => @tac tus tvs nus nvs ctx s e
      | GSolved => Solved s
      | GAll t g =>
        match @runOnGoals tus (tvs ++ t :: nil) nus (S nvs) (CAll ctx t) (AllSubst s) g with
          | Fail => Fail
          | Solved s => Solved (fromAll s)
          | More_ s g => More (fromAll s) (GAll t g)
        end
      | GExs ts sub g =>
        let s' := remembers s ts sub in
        match @runOnGoals (tus ++ ts) tvs (length ts + nus) nvs (CExs ctx ts) s' g with
          | Fail => Fail
          | Solved s'' =>
            let '(shere,cs') := fromExs s'' in
            (** Here I can drop anything that is already instantiated. **)
            if amap_is_full (length ts) shere then
              Solved cs'
            else
              (** TODO(gmalecha): I can be more aggressive here *)
              More_ cs' (GExs ts shere GSolved)
          | More_ s'' g' =>
            let '(shere,cs') := fromExs s'' in
            (** TODO(gmalecha)
             ** Here I need to drop already instantiated vars and
             ** substitute through. Ideally, I should collapse as much
             ** as possible.
             **)
            More_ cs' (GExs ts shere g')
        end
      | GHyp h g =>
        match @runOnGoals tus tvs nus nvs (CHyp ctx h) (HypSubst s) g with
          | Fail => Fail
          | Solved s => Solved (fromHyp s)
          | More_ s g => More_ (fromHyp s) (GHyp h g)
        end
      | GConj_ l r =>
        (** NOTE: It would be nice if I could eagerly
         ** instantiate [r] with any results that came
         ** from [l].
         **)
        match @runOnGoals tus tvs nus nvs ctx s l with
          | Fail => Fail
          | Solved s' => @runOnGoals tus tvs nus nvs ctx s' r
          | More_ s' g' =>
            match @runOnGoals tus tvs nus nvs ctx s' r with
              | Fail => Fail
              | Solved s'' => More s'' g'
              | More_ s'' g'' => More s'' (GConj g' g'')
            end
        end
    end.

  Hypothesis Htac : rtac_sound tac.

  Lemma runOnGoals_sound_ind
  : forall g ctx s,
      @rtac_spec typ expr _ _ _
                 ctx s g
                 (@runOnGoals (getUVars ctx)
                              (getVars ctx)
                              (countUVars ctx)
                              (countVars ctx)
                              ctx s g).
  Proof.
    (** TODO(gmalecha): There really should be a much easier way to
     ** abstract this proof to avoid proving both the case of [Solved]
     ** and the case of [More]
     **)
    induction g; simpl.
    { (* All *)
      intros.
      specialize (IHg (CAll ctx t) (AllSubst s)). simpl in *.
      destruct (runOnGoals (getUVars ctx) (getVars ctx ++ t :: nil)
             (countUVars ctx) (S (countVars ctx)) (AllSubst s) g).
      { constructor. }
      { eapply rtac_spec_All_More; auto. }
      { eauto using rtac_spec_All_Solved. } }
    { intros. specialize (IHg _ (remembers s l a)).
      simpl in IHg.
      destruct (runOnGoals (getUVars ctx ++ l) (getVars ctx)
                           (length l + countUVars ctx) (countVars ctx)
                           (remembers s l a) g).
      { constructor. }
      { rewrite (ctx_subst_eta c).
        simpl fromExs. cbv iota beta.
        eapply rtac_spec_Exs_More.
        auto. }
      { rewrite (ctx_subst_eta c).
        simpl fromExs. cbv iota beta.
        remember (amap_is_full (length l) (fst (fromExs c))).
        destruct b.
        { eapply rtac_spec_remembers_full_Solved; eauto. }
        { eapply rtac_spec_Exs_More; eauto.
          eapply Proper_rtac_spec.
          - reflexivity.
          - symmetry. eapply More_More_. reflexivity.
          - assumption. } } }
    { intros. specialize (IHg _ (HypSubst (t:=e) s)).
      simpl in *.
      destruct (runOnGoals (getUVars ctx) (getVars ctx) (countUVars ctx)
                           (countVars ctx) (HypSubst s) g);
        eauto using rtac_spec_Hyp_More, rtac_spec_Hyp_Solved. }
    { intros. specialize (IHg1 _ s).
      destruct (runOnGoals (getUVars ctx) (getVars ctx) (countUVars ctx)
         (countVars ctx) s g1); eauto.
      { specialize (IHg2 _ c).
        destruct (runOnGoals (getUVars ctx) (getVars ctx) (countUVars ctx)
                             (countVars ctx) c g2); eauto.
        { eapply Proper_rtac_spec.
          - reflexivity.
          - eapply More_More_.
            eapply GConj_GConj_; eauto; reflexivity.
          - eapply rtac_spec_GConj_More_More; eauto. }
        { eapply Proper_rtac_spec.
          - reflexivity.
          - eapply More_More_. reflexivity.
          - eapply rtac_spec_GConj_More_Solved; eauto. } }
      { eapply rtac_spec_GConj_Solved. eauto. eauto. } }
    { (* Goal *)
      clear - Htac; simpl; intros.
      red in Htac.
      specialize (@Htac ctx s e _ eq_refl).
      rewrite countUVars_getUVars.
      rewrite countVars_getVars.
      eauto. }
    { (* Solved *)
      clear. simpl.
      intros. split; auto.
      forward.
      split; [ reflexivity | ].
      intros.
      eapply Pure_pctxD; eauto. }
  Qed.

End runOnGoals.

Arguments runOnGoals {typ expr _ _} tac tus tvs nus nvs ctx csub goal : rename.

Section runOnGoals_proof.
  Context {typ : Type}.
  Context {expr : Type}.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.

  Definition ON_ALL : rtac typ expr -> rtacK typ expr := runOnGoals.

  Theorem runOnGoals_sound
  : forall tac,
      rtac_sound tac -> rtacK_sound (runOnGoals tac).
  Proof.
    intros.
    generalize (@runOnGoals_sound_ind typ expr _ _ _ _ _ tac H).
    red. intros; subst.
    specialize (H0 g ctx s). revert H0; clear.
    unfold rtac_spec, rtacK_spec.
    rewrite countUVars_getUVars.
    rewrite countVars_getVars.
    exact (fun x => x).
  Qed.

  Definition ON_ALL_sound : forall tac, rtac_sound tac -> rtacK_sound (ON_ALL tac)
  := runOnGoals_sound.
End runOnGoals_proof.
