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

Require Import MirrorCore.Util.Quant.
Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section runOnGoals.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Subst_subst : Subst subst expr}.
  Context {SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst}.
  Context {SubstUpdate_subst : SubstUpdate subst expr}.
  Context {SubstUpdateOk_subst : @SubstUpdateOk _ _ _ _ Expr_expr Subst_subst _ _}.

  Variable tac : rtac typ expr subst.

  Fixpoint runOnGoals (tus tvs : tenv typ) (nus nvs : nat)
           (ctx : Ctx typ expr) (s : ctx_subst subst ctx) (g : Goal typ expr)
           {struct g}
  : Result subst ctx :=
    match g with
      | GGoal e => @tac tus tvs nus nvs ctx s e
      | GSolved => Solved s
      | GAll t g =>
        match @runOnGoals tus (tvs ++ t :: nil) nus (S nvs) (CAll ctx t) (AllSubst s) g with
          | Fail => Fail
          | Solved s => Solved (fromAll s)
          | More_ s g => More (fromAll s) (GAll t g)
        end
      | GExs tes g =>
        (* TODO: Is it meaningful to make this a [list typ * subst]?
          match remembers nus tes s with
            | None => Fail
            | Some s' =>
         *)
        let ts := map fst tes in
        (** TODO: This returning an error is redundant **)
        match remembers nus tes (@empty _ _ _) with
          | None => Fail
          | Some s' =>
            let s' := ExsSubst s s' in
            match @runOnGoals (tus ++ ts) tvs (length tes + nus) nvs (CExs ctx ts) s' g with
              | Fail => Fail
              | Solved s'' =>
                let '(shere,cs') := fromExs s'' in
                (** Here I can drop anything that is already instantiated. **)
                let tes' := forgets nus ts shere in
                let tes' := combine ts tes' in
                More_ cs' (GExs tes' GSolved)
              | More_ s'' g' =>
                let '(shere,cs') := fromExs s'' in
                (** Here I need to drop already instantiated vars and
                 ** substitute through. Ideally, I should collapse as much
                 ** as possible.
                 **)
                let tes' := forgets nus ts shere in
                let tes' := combine ts tes' in
                More_ cs' (GExs tes' g')
            end
        end
      | GHyp h g =>
        match @runOnGoals tus tvs nus nvs (CHyp ctx h) (HypSubst s) g with
          | Fail => Fail
          | Solved s => Solved (fromHyp s)
          | More_ s g => More_ (fromHyp s) (GHyp h g)
        end
      | GConj_ l r =>
        match @runOnGoals tus tvs nus nvs ctx s l with
          | Fail => Fail
          | Solved s' => @runOnGoals tus tvs nus nvs ctx s' r
          | More_ s' g' =>
            match @runOnGoals tus tvs nus nvs ctx s' r with
              | Fail => Fail
              | Solved s'' => More s'' g'
              | More_ s'' g'' => More s'' (GConj_ g' g'')
            end
        end
    end.

    Variables tus tvs : tenv typ.
    Hypothesis Htac : rtac_sound tus tvs tac.

    Lemma WellFormed_remembers
    : forall a b s s',
        remembers (typ:=typ) a b s = Some s' ->
        WellFormed_subst s ->
        WellFormed_subst s'.
    Admitted.

(*
    Lemma remembers_forgets_safe
    : forall tes s s' s'' sD es eD,
        remembers (length tus) tes s = Some s' ->
        forgets (length tus) (map fst tes) s' = (s'',es) ->
        substD tus tvs s = Some sD ->
        goal_substD tus tvs (map fst tes) (map snd tes) = Some eD ->
        exists eD',
          goal_substD tus tvs (map fst tes) es = Some eD'.
    Proof.
      clear Htac tac.
      induction tes; simpl; intros; inv_all; subst; eauto.
      forward. subst. simpl in *.
      inv_all; subst.
      destruct o0; forward; inv_all; subst.
      { (*

        eapply forget_sound in H3; eauto.
        forward_reason.
        specialize (@H5 _ _ _ _ H1).
*)
    Admitted.
*)

    Local Hint Constructors WellFormed_ctx_subst.
    Lemma WellFormed_ctx_subst_fromAll
    : forall t c cs,
        @WellFormed_ctx_subst typ expr subst _ _ _ _ (CAll c t) cs ->
        @WellFormed_ctx_subst typ expr subst _ _ _ _ c (fromAll cs).
    Proof.
      intros.
      refine match H in @WellFormed_ctx_subst _ _ _ _ _ _ _ C S
                   return match C as C return ctx_subst subst C -> Prop with
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
        @WellFormed_ctx_subst typ expr subst _ _ _ _ (CHyp c t) cs ->
        @WellFormed_ctx_subst typ expr subst _ _ _ _ c (fromHyp cs).
    Proof.
      intros.
      refine match H in @WellFormed_ctx_subst _ _ _ _ _ _ _ C S
                   return match C as C return ctx_subst subst C -> Prop with
                            | CHyp _ _ => fun x => WellFormed_ctx_subst (fromHyp x)
                            | _ => fun _ => True
                          end S
             with
               | WF_HypSubst _ _ _ pf => pf
               | _ => I
             end.
    Qed.
    Local Hint Resolve WellFormed_ctx_subst_fromAll WellFormed_ctx_subst_fromHyp.

    Lemma runOnGoals_sound_ind
    : forall g ctx s,
        @rtac_spec typ expr subst _ _ _ _ _
                   tus tvs ctx s g
                   (@runOnGoals (tus ++ getUVars ctx)
                                (tvs ++ getVars ctx)
                                (length tus + countUVars ctx)
                                (length tvs + countVars ctx)
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
        destruct (runOnGoals (tus ++ getUVars ctx) (tvs ++ getVars ctx ++ t :: nil)
                             (length tus + countUVars ctx) (length tvs + S (countVars ctx))
                             (AllSubst s) g);
          auto; intros; forward_reason; split; eauto.
        { generalize (Proper_pctxD_impl tus tvs (fromAll c)).
          simpl in *.
          rewrite goalD_conv with (pfu := eq_refl)
                                  (pfv := eq_sym (app_ass_trans tvs (getVars ctx) (t :: nil))).
          autorewrite with eq_rw.
          forward; inv_all; subst.
          forward_reason.
          inv_all; subst; simpl in *.
          forward; inv_all; subst.
          split; eauto.
          intros us vs.
          eapply H4; [ | reflexivity | reflexivity | eapply H7 ].
          do 6 red. clear.
          do 6 intro; equivs.
          destruct (app_ass_trans tvs (getVars ctx) (t :: nil)); simpl.
          eauto. }
        { generalize (Proper_pctxD_impl tus tvs (fromAll c)).
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
          simpl in *; eauto. } }
      { (* Exs *)
(*
        intros; simpl in *.
        forward.
        specialize (IHg (CExs ctx (map fst l)) s0).
        revert IHg. revert H; simpl.
        repeat rewrite countUVars_getUVars.
        repeat rewrite countVars_getVars.
        do 2 rewrite <- app_length.
        intros; forward.
        match goal with
          | H : match ?X with _ => _ end |- match match ?Y with _ => _ end with _ => _ end =>
            replace Y with X;
              [ remember X as X' ; destruct X'
              | f_equal ; simpl; repeat rewrite app_length;
                rewrite map_length; omega ]
        end; intros; auto;
        match goal with
          | |- context [ forgets ?A ?B ?C ] =>
            consider (forgets A B C)
        end; intros; simpl in *.
        { consider (forgets (length (tus ++ getUVars ctx)) (map fst l) s0); intros; auto.
          inv_all; subst.
          generalize (WellFormed_remembers _ _ _ H H4); intros.
          forward_reason.
          split; [ eapply WellFormed_forgets; eauto | ].
          forward. inv_all; subst.
          revert H8. revert H9.

              inv_all; subst
            { admit. }


          admit. }
        { consider (forgets (length tus + countUVars ctx) (map fst l) s1); intros; auto.
          inv_all; subst.
          admit. } *) admit. }
      { (* Hyp *)
        simpl; intros.
        specialize (IHg (CHyp ctx e) (HypSubst s)).
        match goal with
          | H : match ?X with _ => _ end
            |- match match ?Y with _ => _ end with _ => _ end =>
            replace Y with X; [ remember X as X' ; destruct X' | f_equal ; simpl ; rewrite map_length; omega ]
        end; auto;
        intros; forward_reason; split; eauto; simpl in *;
        forward; forward_reason; subst; inv_all; subst; simpl in *;
        forward; subst; inv_all; subst.
        { split; auto.
          intros us vs.
          generalize (H7 us vs).
          eapply Fmap_pctxD_impl; try reflexivity; eauto.
          clear; do 6 red; intros.
          equivs; tauto. }
        { split; auto. } }
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
          { rename g into B'.
            intros; forward_reason; split; auto.
            simpl. forward. forward_reason.
            split; [ etransitivity; eassumption | ].
            intros us vs.
            specialize (H11 us vs).
            specialize (H12 us vs).
            revert H11.
            eapply (Applicative_pctxD _ H8).
            eapply pctxD_SubstMorphism.
            3: eassumption. eassumption. eassumption.
            revert H12.
            eapply (Fmap_pctxD_impl _ H3); try reflexivity.
            clear. do 6 red.
            intros. equivs. firstorder. }
          { change (rtac_spec tus tvs s (GConj_ A B) (More c0 A')).
            eapply Proper_rtac_spec; [ reflexivity | eapply More_More_ | ].
            reflexivity.
            simpl.
            intros; forward_reason; split; auto.
            simpl. forward. forward_reason.
            split; [ etransitivity; eassumption | ].
            intros us vs.
            specialize (H11 us vs).
            specialize (H10 us vs).
            revert H10.
            eapply (Applicative_pctxD _ H8).
            eapply pctxD_SubstMorphism.
            3: eassumption. eassumption. eassumption.
            revert H11.
            eapply (Fmap_pctxD_impl _ H3); try reflexivity.
            clear. do 6 red.
            intros. equivs. firstorder. } }
        { specialize (IHg2 ctx c).
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
            intros. equivs. firstorder. } } }
      { (* Goal *)
        clear - Htac; simpl; intros.
        red in Htac.
        specialize (@Htac ctx s e _ eq_refl).
        rewrite countUVars_getUVars.
        rewrite countVars_getVars.
        do 2 rewrite <- app_length.
        eauto. }
      { (* Solved *)
        clear. simpl.
        intros. split; auto.
        forward. split; [ reflexivity | ].
        intros.
        eapply (@Applicative_pctxD _ _ _ _ _ _ _ _ tus tvs ctx s); eauto. }
    Qed.

    Theorem runOnGoals_sound ctx s g
    : @rtac_spec _ _ _ _ _ _ _ _ tus tvs ctx s g
                 (@runOnGoals (tus ++ getUVars ctx)
                              (tvs ++ getVars ctx)
                              (length tus + countUVars ctx)
                              (length tvs + countVars ctx)
                              ctx s g).
    Proof.
      eapply runOnGoals_sound_ind.
    Qed.

End runOnGoals.

Arguments runOnGoals {typ expr subst _ _} tac tus tvs nus nvs ctx csub goal : rename.
