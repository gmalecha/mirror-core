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

Require Import MirrorCore.Util.Quant.
Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section runOnGoals.
  Variable typ : Type.
  Variable expr : Type.

  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.

  Lemma iff_to_eq : forall P Q : Prop, P = Q -> (P <-> Q).
  Proof. clear; intros; subst; reflexivity. Qed.


  Lemma map_fst_combine : forall {T U} (ts : list T) (us : list U),
                            length ts = length us ->
                            map fst (combine ts us) = ts.
  Proof.
    clear.
    induction ts; simpl; intros; auto.
    destruct us. inversion H.
    simpl. f_equal. auto.
  Qed.

  Lemma map_snd_combine : forall {T U} (ts : list T) (us : list U),
                            length ts = length us ->
                            map snd (combine ts us) = us.
  Proof.
    clear.
    induction ts; destruct us; simpl; intros; auto.
    congruence. f_equal. auto.
  Qed.

  Lemma eta_ctx_subst_exs c ts (s : ctx_subst (CExs c ts))
  : exists y z,
      s = ExsSubst (typ:=typ) (expr:=expr) z y.
  Proof.
    refine (match s in @ctx_subst _ _ X
                  return match X as X return @ctx_subst _ _ X -> Prop with
                           | CExs c ts => fun s =>
                             exists (y : _) (z : ctx_subst  c), s = ExsSubst z y
                           | _ => fun _ => True
                         end s
            with
              | ExsSubst _ _ _ s => _
              | _ => I
            end).
    eauto.
  Qed.

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
        let s' := ExsSubst s sub in
        match @runOnGoals (tus ++ ts) tvs (length ts + nus) nvs (CExs ctx ts) s' g with
          | Fail => Fail
          | Solved s'' =>
            let '(shere,cs') := fromExs s'' in
            (** Here I can drop anything that is already instantiated. **)
            More_ cs' (GExs ts shere GSolved)
          | More_ s'' g' =>
            let '(shere,cs') := fromExs s'' in
            (** Here I need to drop already instantiated vars and
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
              | More_ s'' g'' => More_ s'' (GConj_ g' g'')
            end
        end
    end.

  Fixpoint runOnGoals_list (tacs : list (rtac typ expr)) (tus tvs : tenv typ) (nus nvs : nat)
           (ctx : Ctx typ expr) (s : ctx_subst ctx) (g : Goal typ expr)
           {struct g}
  : Result ctx * list (rtac typ expr) :=
    match g with
      | GGoal e =>
        match tacs with
          | nil => (Fail, nil)
          | tac :: tacs => (@tac tus tvs nus nvs ctx s e, tacs)
        end
      | GSolved => (Solved s, tacs)
      | GAll t g =>
        match @runOnGoals_list tacs tus (tvs ++ t :: nil) nus (S nvs) (CAll ctx t) (AllSubst s) g with
          | (Fail, tacs) => (Fail,tacs)
          | (Solved s, tacs) => (Solved (fromAll s), tacs)
          | (More_ s g, tacs) => (More (fromAll s) (GAll t g), tacs)
        end
      | GExs ts sub g =>
        let s' := ExsSubst s sub in
            match @runOnGoals_list tacs (tus ++ ts) tvs (length ts + nus) nvs (CExs ctx ts) s' g with
              | (Fail, tacs) => (Fail, tacs)
              | (Solved s'', tacs) =>
                let '(shere,cs') := fromExs s'' in
                (** Here I can drop anything that is already instantiated. **)
                (More_ cs' (GExs ts shere GSolved), tacs)
              | (More_ s'' g', tacs) =>
                let '(shere,cs') := fromExs s'' in
                (** Here I need to drop already instantiated vars and
                 ** substitute through. Ideally, I should collapse as much
                 ** as possible.
                 **)
                (More_ cs' (GExs ts shere g'), tacs)
            end
      | GHyp h g =>
        match @runOnGoals_list tacs tus tvs nus nvs (CHyp ctx h) (HypSubst s) g with
          | (Fail, tacs) => (Fail, tacs)
          | (Solved s, tacs) => (Solved (fromHyp s), tacs)
          | (More_ s g, tacs) => (More_ (fromHyp s) (GHyp h g), tacs)
        end
      | GConj_ l r =>
        (** NOTE: It would be nice if I could eagerly
         ** instantiate [r] with any results that came
         ** from [l].
         **)
        match @runOnGoals_list tacs tus tvs nus nvs ctx s l with
          | (Fail, tacs) => (Fail, tacs)
          | (Solved s', tacs) => @runOnGoals_list tacs tus tvs nus nvs ctx s' r
          | (More_ s' g', tacs) =>
            match @runOnGoals_list tacs tus tvs nus nvs ctx s' r with
              | (Fail, tacs) => (Fail, tacs)
              | (Solved s'', tacs) => (More s'' g', tacs)
              | (More_ s'' g'', tacs) => (More s'' (GConj_ g' g''), tacs)
            end
        end
    end.

  Hypothesis Htac : rtac_sound tac.

  Local Hint Constructors WellFormed_ctx_subst.
  Lemma WellFormed_ctx_subst_fromAll
  : forall t c cs,
      @WellFormed_ctx_subst typ expr _ _ (CAll c t) cs ->
      @WellFormed_ctx_subst typ expr _ _ c (fromAll cs).
  Proof.
    intros.
    refine match H in @WellFormed_ctx_subst _ _ _ _ C S
                 return match C as C return ctx_subst C -> Prop with
                          | CAll _ _ => fun x => WellFormed_ctx_subst (fromAll x)
                          | _ => fun _ => True
                        end S
           with
             | WF_AllSubst _ _ _ pf => pf
             | _ => I
           end.
  Qed.
  Lemma WellFormed_ctx_subst_fromHyp
  : forall t c cs,
      @WellFormed_ctx_subst typ expr _ _ (CHyp c t) cs ->
      @WellFormed_ctx_subst typ expr _ _ c (fromHyp cs).
  Proof.
    intros.
    refine match H in @WellFormed_ctx_subst _ _ _ _ C S
                 return match C as C return ctx_subst C -> Prop with
                          | CHyp _ _ => fun x => WellFormed_ctx_subst (fromHyp x)
                          | _ => fun _ => True
                        end S
           with
             | WF_HypSubst _ _ _ pf => pf
             | _ => I
           end.
  Qed.
  Local Hint Resolve WellFormed_ctx_subst_fromAll WellFormed_ctx_subst_fromHyp.


(*
  Lemma runOnGoals_list_sound_ind
  : forall tacs g ctx s,
      Forall (rtac_sound tus tvs) tacs ->
      @rtac_spec typ expr subst _ _ _ _ _
                 tus tvs ctx s g
                 (@runOnGoals_list tacs
                                   (tus ++ getUVars ctx)
                                   (tvs ++ getVars ctx)
                                   (length tus + countUVars ctx)
                                   (length tvs + countVars ctx)
                                   ctx s g).
*)


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
    red. induction g; fold runOnGoals in *.
    { (* All *)
      intros.
      specialize (@IHg (CAll ctx t) (AllSubst s)).
      simpl in *.
      match goal with
        | H : match ?X with _ => _ end |- match match ?Y with _ => _ end with _ => _ end =>
          replace Y with X
      end; [ | f_equal ; try solve [ rewrite app_ass_trans ; reflexivity | omega ] ].
      destruct (runOnGoals (getUVars ctx) (getVars ctx ++ t :: nil)
                           (countUVars ctx) (S (countVars ctx))
                           (AllSubst s) g);
        auto; intros; forward_reason; inv_all.
      { destruct IHg as [ ? [ ? ? ] ].
        { assumption. }
        { constructor. auto. }
        split.
        { apply WellFormed_ctx_subst_fromAll; auto. }
        split.
        { constructor. eauto. }
        { generalize (Proper_pctxD_impl (fromAll c)).
          simpl in *.
          forward; inv_all; subst.
          forward_reason.
          inv_all; subst; simpl in *.
          forward; inv_all; subst.
          split; eauto.
          intros us vs.
          eapply H6; [ | reflexivity | reflexivity | eapply H9 ].
          do 6 red. clear.
          do 6 intro; equivs.
          eauto. } }
      { admit. (* generalize (Proper_pctxD_impl tus tvs (fromAll c)).
        simpl in *.
        rewrite goalD_conv with (pfu := eq_refl)
                                  (pfv := eq_sym (app_ass_trans tvs (getVars ctx) (t :: nil))).
        autorewrite with eq_rw.
        forward; inv_all; subst.
        forward_reason.
        inv_all; subst; simpl in *.
        forward; inv_all; subst.
        split; eauto. intros.
        generalize (H6 us vs).
        eapply Fmap_pctxD_impl; eauto; try reflexivity.
        clear.
        do 6 red. intros; equivs.
        destruct (app_ass_trans tvs (getVars ctx) (t :: nil)).
        simpl in *; eauto. } *) } }
    { (* Exs *)
      intros; simpl in *.
      forward.
      specialize (@IHg (CExs _ l) (ExsSubst s a)).
      revert IHg.
      repeat rewrite countUVars_getUVars.
      repeat rewrite countVars_getVars.
      intros; forward.
      match goal with
        | H : match ?X with _ => _ end |- match match ?Y with _ => _ end with _ => _ end =>
          replace Y with X;
            [ remember X as X' ; destruct X'
            | simpl; f_equal; rewrite app_length; omega ]
      end; intros; auto.
      { destruct (eta_ctx_subst_exs c) as [ ? [ ? ? ] ]; subst.
        simpl. intros.
        destruct IHg as [ ? [ ? ? ] ].
        { inversion H; subst; auto. }
        { inversion H; subst. constructor; auto.
          rewrite countUVars_getUVars. assumption. }
        simpl in *.
        forward.
        inv_all.
        inv_all.
        split; auto. split.
        { constructor; eauto.
          rewrite countUVars_getUVars in H8. assumption. }
        { forward. inv_all. subst.
          forward_reason. inv_all; subst.
          revert H12.
          Cases.rewrite_all_goal. intros.
          split; auto. reflexivity.
          intros.
          generalize (H14 us vs); clear H14.
          eapply Ap_pctxD; eauto.
          generalize (H12 us vs); clear H12.
          eapply Fmap_pctxD_impl; eauto; try reflexivity.
          clear.
          do 6 red; intros.
          eapply _exists_sem.
          eapply _exists_sem in H3. destruct H3.
          exists x1.
          rewrite _forall_sem in H2.
          equivs. firstorder. } }
      { destruct (eta_ctx_subst_exs c) as [ ? [ ? ? ] ]; subst.
        simpl. intros.
        inv_all.
        destruct IHg as [ ? ? ]; eauto.
        { constructor; eauto. rewrite countUVars_getUVars. assumption. }
        inv_all.
        split; auto. split.
        { constructor; auto. rewrite <- countUVars_getUVars. assumption.
          constructor. }
        simpl in *.
        forward. inv_all; subst.
        forward_reason. inv_all; subst.
        split; auto.
        intros.
        revert H10.
        Cases.rewrite_all_goal. intros.
        generalize (H10 us vs); clear H10.
        eapply Ap_pctxD; eauto.
        generalize (H12 us vs); clear H12.
        eapply Fmap_pctxD_impl; eauto; try reflexivity.
        clear.
        do 6 red. intros.
        eapply _exists_sem.
        eapply _exists_sem in H3. destruct H3.
        exists x1.
        rewrite _forall_sem in H1.
        equivs. firstorder. } }
    { (* Hyp *)
      simpl; intros.
      specialize (IHg (CHyp ctx e) (HypSubst s)).
      simpl in *.
      match goal with
        | H : match ?X with _ => _ end
          |- match match ?Y with _ => _ end with _ => _ end =>
          replace Y with X; [ remember X as X' ; destruct X' | f_equal ; simpl ; rewrite map_length; omega ]
      end; auto.
      { admit. }
      { admit. } }
    { (* Conj *)
      simpl; intros; clear Htac.
      specialize (IHg1 ctx s).
      rename g1 into A.
      rename g2 into B.
      match goal with
        | H : match ?X with _ => _ end
          |- context [ match ?Y with _ => _ end ] =>
          change Y with X ; destruct X; auto
      end.
      { rename g into A'.
        specialize (IHg2 ctx c).
        match goal with
          | H : match ?X with _ => _ end
            |- context [ match ?Y with _ => _ end ] =>
            change Y with X ; destruct X; auto
        end.
        { 
          Global Instance Injective_WellFormed_Goal_GConj tus tvs a b
          : Injective (WellFormed_Goal tus tvs (GConj_ a b)) :=
          { result := WellFormed_Goal tus tvs a /\ WellFormed_Goal tus tvs b }.
          Proof. inversion 1. auto. Defined.
          intros; inv_all.
          forward_reason.
          split; auto.
          split; [ constructor; auto | ].
          simpl. forward. forward_reason.
          split; [ etransitivity; eauto | ].
          intros us vs.
          generalize (H15 us vs); clear H15.
          eapply Ap_pctxD; eauto.
          eapply pctxD_SubstMorphism; eauto.
          generalize (H16 us vs); clear H16.
          eapply Fmap_pctxD_impl; eauto; try reflexivity.
          clear. do 6 red.
          intros. equivs. firstorder. }
        { change (rtac_spec s (GConj_ A B) (More c0 A')).
          eapply Proper_rtac_spec; [ reflexivity | eapply More_More_ | ].
          reflexivity.
          simpl.
          intros; inv_all; forward_reason.
          split; auto. split; auto.
          forward. forward_reason.
          split; [ etransitivity; eassumption | ].
          intros us vs.
          generalize (H13 us vs); clear H13.
          eapply Ap_pctxD; eauto.
          eapply pctxD_SubstMorphism; eauto.
          generalize (H14 us vs); clear H14.
          eapply Fmap_pctxD_impl; eauto; try reflexivity.
          clear. do 6 red.
          intros. equivs. firstorder. } }
      { admit. (* specialize (IHg2 ctx c).
        match goal with
          | H : match ?X with _ => _ end
            |- context [ match ?Y with _ => _ end ] =>
            change Y with X ; destruct X; auto
        end.
        { rename g into B'.
          intros; forward_reason; split; auto.
          simpl. forward. forward_reason.
          split; [ etransitivity; eassumption | ].
          intros us vs.
          specialize (H10 us vs).
          specialize (H11 us vs).
          revert H10.
          eapply (Applicative_pctxD _ H7).
          eapply pctxD_SubstMorphism.
          3: eassumption. eassumption. eassumption.
          revert H11.
          eapply (Fmap_pctxD_impl _ H3); try reflexivity.
          clear. do 6 red.
          intros. equivs. firstorder. }
        { intros; forward_reason; split; auto.
          simpl. forward. forward_reason.
          split; [ etransitivity; eassumption | ].
          intros us vs.
          specialize (H9 us vs).
          specialize (H10 us vs).
          revert H9.
          eapply (Applicative_pctxD _ H7).
          eapply pctxD_SubstMorphism.
          3: eassumption. eassumption. eassumption.
          revert H10.
          eapply (Fmap_pctxD_impl _ H3); try reflexivity.
          clear. do 6 red.
          intros. equivs. firstorder. } } *) } }
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

Arguments runOnGoals {typ expr} tac tus tvs nus nvs ctx csub goal : rename.

Section runOnGoals_proof.
  Variable typ : Type.
  Variable expr : Type.

  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.

  Theorem runOnGoals_sound
  : forall tac,
      rtac_sound tac -> rtacK_sound (runOnGoals tac).
  Proof.
    intros.
    generalize (@runOnGoals_sound_ind typ expr _ _ _ tac H).
    red. intros; subst.
    specialize (H0 g ctx s). revert H0; clear.
    unfold rtac_spec, rtacK_spec.
    rewrite countUVars_getUVars.
    rewrite countVars_getVars.
    exact (fun x => x).
  Qed.
End runOnGoals_proof.