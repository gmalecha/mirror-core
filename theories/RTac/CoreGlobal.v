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
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.RTac.Core.

Require Import MirrorCore.Util.Quant.
Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
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

  Fixpoint ctxD (tus tvs : tenv typ) (ctx : Ctx typ expr) (s : ctx_subst subst ctx)
           {struct s}
  : option (   exprT (tus ++ getUVars ctx) (tvs ++ getVars ctx) Prop
            -> exprT tus tvs Prop) :=
    match s in ctx_subst _ ctx
          return option (   exprT (tus ++ getUVars ctx) (tvs ++ getVars ctx) Prop
                         -> exprT tus tvs Prop)
    with
      | TopSubst s =>
        match substD tus tvs s with
          | None => None
          | Some sD =>
            Some (fun (k : exprT _ _ Prop) us vs =>
                    sD us vs /\
                    k (hlist_app us Hnil) (hlist_app vs Hnil))
        end
      | AllSubst t ctx' s' =>
        match ctxD tus tvs s' with
          | Some cD =>
            Some (fun k : exprT _ _ Prop =>
                    cD (fun us vs =>
                          forall x : typD t,
                            k us
                              match
                                app_ass_trans tvs (getVars ctx') (t :: nil) in (_ = t0)
                                return (hlist typD t0)
                              with
                                | eq_refl => hlist_app vs (Hcons x Hnil)
                              end))
          | None => None
        end
      | ExsSubst ts ctx' s' sub =>
        match substD ((tus ++ getUVars ctx') ++ ts) (tvs ++ getVars ctx') sub
            , ctxD tus tvs s'
        with
          | Some sD , Some cD =>
            Some (fun k : exprT (tus ++ getUVars ctx' ++ ts) (tvs ++ getVars ctx') Prop =>
                    cD (fun us vs =>
                          _exists typD ts (fun us' =>
                                             sD (hlist_app us us') vs /\
                                             k match
                                                 app_ass_trans tus _ ts in (_ = t0)
                                                 return (hlist typD t0)
                                               with
                                                 | eq_refl => hlist_app us us'
                                               end
                                               vs)))
          | _ , _ => None
        end
      | HypSubst h ctx' s' =>
        match propD (tus ++ getUVars ctx') (tvs ++ getVars ctx') h with
          | None => None
          | Some pD => match ctxD tus tvs s' with
                         | None => None
                         | Some cD =>
                           Some (fun k : exprT _ _ Prop =>
                                   cD (fun us vs => pD us vs -> k us vs))
                       end
        end
    end.

  Definition rtac_global_spec tus tvs ctx (s : ctx_subst subst ctx) g (r : Result _ ctx) : Prop :=
    match r with
      | Fail => True
      | Solved s' =>
        WellFormed_ctx_subst s ->
        WellFormed_ctx_subst s' /\
        match @ctxD tus tvs ctx s
            , goalD _ _ g
            , @ctxD tus tvs ctx s'
        with
          | None , _ , _
          | Some _ , None , _ => True
          | Some _ , Some _ , None => False
          | Some cD , Some gD , Some cD' =>
            forall us vs,
              cD' (fun _ _ => True) us vs -> cD gD us vs
        end
      | More_ s' g' =>
        WellFormed_ctx_subst s ->
        WellFormed_ctx_subst s' /\
        match @ctxD tus tvs ctx s
            , goalD _ _ g
            , @ctxD tus tvs ctx s'
            , goalD _ _ g'
        with
          | None , _ , _ , _
          | Some _ , None , _ , _ => True
          | Some _ , Some _ , None , _
          | Some _ , Some _ , Some _ , None => False
          | Some cD , Some gD , Some cD' , Some gD' =>
            forall us vs, cD' gD' us vs -> cD gD us vs
        end
    end.

  Ltac equivs :=
    repeat match goal with
             | H : equiv_hlist _ _ _ |- _ => apply equiv_eq_eq in H
           end; subst.

  Theorem Proper_rtac_global_spec tus tvs ctx s
  : Proper (EqGoal (tus ++ getUVars ctx) (tvs ++ getVars ctx) ==>
            @EqResult _ _ _ _ _ _ (tus ++ getUVars ctx) (tvs ++ getVars ctx) ctx
            ==> iff)
           (@rtac_global_spec tus tvs ctx s).
  Proof.
(*
    red. red. red.
    unfold rtac_spec.
    unfold EqGoal.
    unfold EqResult.
    intros. unfold subst_ctxD.
    inversion H0; clear H0.
    { destruct x0; simpl in *; try congruence.
      destruct y0; simpl in *; try congruence.
      reflexivity. }
    { destruct x0; simpl in *; try congruence;
      destruct y0; simpl in *; try congruence; inv_all; subst;
      inversion H3; clear H3; subst;
      repeat match goal with
               | |- (_ -> _) <-> (_ -> _) =>
                 apply impl_iff; [ reflexivity | intro ]
               | |- (_ /\ _) <-> (_ /\ _) =>
                 apply and_iff; [ reflexivity | intro ]
             end.
      { red in H6.
        generalize (Proper_pctxD tus tvs ctx s).
        generalize (Proper_pctxD tus tvs ctx s1).
        destruct (pctxD tus tvs ctx s); try reflexivity.
        destruct p.
        destruct (substD tus tvs s0); try reflexivity.
        inversion H; try reflexivity.
        destruct (pctxD tus tvs ctx s1); try reflexivity.
        destruct p.
        destruct (substD tus tvs s2); try reflexivity.
        inversion H6; clear H6; try reflexivity.
        inversion 1; inversion 1; subst.
        inversion H11; inversion H15; subst.
        do 2 (apply forall_iff; intro).
        apply impl_iff.
        { apply and_iff. reflexivity. intro.
          eapply H17. assumption. reflexivity. reflexivity. }
        { intro. apply and_iff. reflexivity. intro.
          eapply H23. assumption. reflexivity. reflexivity. } }
      { red in H6.
        simpl in H6.
        generalize (Proper_pctxD tus tvs ctx s).
        generalize (Proper_pctxD tus tvs ctx s1).
        destruct (pctxD tus tvs ctx s); try reflexivity.
        destruct p.
        destruct (substD tus tvs s0); try reflexivity.
        inversion H; try reflexivity.
        destruct (pctxD tus tvs ctx s1); try reflexivity.
        destruct p.
        destruct (substD tus tvs s2); try reflexivity.
        inversion H6; clear H6; try reflexivity.
        inversion 1; inversion 1; subst.
        inversion H11; inversion H15; subst.
        do 2 (apply forall_iff; intro).
        eapply impl_iff.
        { apply and_iff. reflexivity. intro.
          eapply H16. assumption. reflexivity. reflexivity. }
        { intro. apply and_iff. reflexivity. intro.
          eapply H22. assumption. reflexivity. reflexivity. } }
      { red in H6.
        simpl in H6.
        generalize (Proper_pctxD tus tvs ctx s).
        generalize (Proper_pctxD tus tvs ctx s1).
        destruct (pctxD tus tvs ctx s); try reflexivity.
        destruct p.
        destruct (substD tus tvs s0); try reflexivity.
        inversion H; try reflexivity.
        destruct (pctxD tus tvs ctx s1); try reflexivity.
        destruct p.
        destruct (substD tus tvs s2); try reflexivity.
        inversion H6; clear H6; try reflexivity.
        inversion 1; inversion 1; subst.
        inversion H11; inversion H15; subst.
        do 2 (apply forall_iff; intro).
        eapply impl_iff.
        { apply and_iff. reflexivity. intro.
          eapply H16. assumption. reflexivity. reflexivity. }
        { intro. apply and_iff. reflexivity. intro.
          eapply H22. assumption. reflexivity. reflexivity. } }
      { red in H6.
        simpl in H6.
        generalize (Proper_pctxD tus tvs ctx s).
        generalize (Proper_pctxD tus tvs ctx s1).
        destruct (pctxD tus tvs ctx s); try reflexivity.
        destruct p.
        destruct (substD tus tvs s0); try reflexivity.
        inversion H; try reflexivity.
        destruct (pctxD tus tvs ctx s1); try reflexivity.
        destruct p.
        destruct (substD tus tvs s2); try reflexivity.
        inversion H6; clear H6; try reflexivity.
        inversion 1; inversion 1; subst.
        inversion H11; inversion H15; subst.
        do 2 (apply forall_iff; intro).
        eapply impl_iff.
        { apply and_iff. reflexivity. intro.
          eapply H14. assumption. reflexivity. reflexivity. }
        { intro. apply and_iff. reflexivity. intro.
          eapply H21. assumption. reflexivity. reflexivity. } } }
*)
  Abort.

  Definition rtac_global_sound (tus tvs : tenv typ) (tac : rtac typ expr subst)
  : Prop :=
    forall ctx s g result,
      (let tus := tus ++ getUVars ctx in
       let tvs := tvs ++ getVars ctx in
       tac tus tvs (length tus) (length tvs) ctx s g = result) ->
      @rtac_spec typ expr subst _ _ _ _ _ tus tvs ctx s (GGoal g) result.

  Lemma pctxD_ctxD
  : forall tus tvs ctx s pC C,
      pctxD tus tvs s = Some pC ->
      @ctxD tus tvs ctx s = Some C ->
      forall us vs (P Q : exprT _ _ Prop),
        pC (fun a b => P a b -> Q a b) us vs ->
        C P us vs -> C Q us vs.
  Proof.
(*
    clear. induction s; simpl; intros; inv_all; subst; forward; inv_all; subst.
    { firstorder. }
    { revert H2. eapply IHs; eauto.
      revert H1.
      eapply Fmap_pctxD_impl; eauto; try reflexivity.
      clear.
      do 6 red. intros; equivs. firstorder. }
    { revert H2. eapply IHs; eauto.
      revert H1.
      eapply Fmap_pctxD_impl; eauto; try reflexivity.
      clear.
      do 6 red. intros; equivs. firstorder. }
    { revert H2.
      eapply IHs; eauto.
      revert H1.
      eapply Fmap_pctxD_impl; eauto; try reflexivity.
      clear.
      do 6 red; intros; equivs.
      rewrite _exists_sem.
      rewrite _exists_sem in H2.
      destruct H2 as [ v ? ]; exists v.
      rewrite _forall_sem in H1.
      specialize (H1 v).
      firstorder. }
*)
  Abort.

  Lemma pctxD_ctxD_safe
  : forall tus tvs ctx s P,
      pctxD tus tvs s = Some P ->
      exists P',
        @ctxD tus tvs ctx s = Some P'.
  Proof.
    induction s; simpl; intros; forward; inv_all; subst; eauto;
    try (specialize (IHs _ eq_refl)); forward_reason; Cases.rewrite_all_goal;
    eauto.
  Qed.

  Lemma ctxD_pctxD_safe
  : forall tus tvs ctx s P,
      @ctxD tus tvs ctx s = Some P ->
      exists P',
        pctxD tus tvs s = Some P'.
  Proof.
    induction s; simpl; intros; forward; inv_all; subst; eauto;
    try (specialize (IHs _ eq_refl)); forward_reason; Cases.rewrite_all_goal;
    eauto.
  Qed.

  Lemma pctxD_to_ctxD
  : forall tus tvs ctx s pC,
      pctxD tus tvs s = Some pC ->
      exists C,
        @ctxD tus tvs ctx s = Some C /\
        forall us vs (P Q : exprT _ _ Prop),
          pC (fun a b => P a b -> Q a b) us vs ->
          C P us vs -> C Q us vs.
  Proof.
    clear. intros.
    destruct (pctxD_ctxD_safe _ H).
    eexists; split; eauto.
    apply (pctxD_ctxD _ H H0).
  Qed.

  Lemma ctxD_to_pctxD
  : forall tus tvs ctx s C,
      @ctxD tus tvs ctx s = Some C ->
      exists pC,
        pctxD tus tvs s = Some pC /\
        forall us vs (P Q : exprT _ _ Prop),
          pC (fun a b => P a b -> Q a b) us vs ->
          C P us vs -> C Q us vs.
  Proof.
    clear. intros.
    destruct (ctxD_pctxD_safe _ H).
    eexists; split; eauto.
    apply (pctxD_ctxD _ H0 H).
  Qed.

(*
  Lemma Proper_ctxD_iff tus tvs ctx s
  : Proper (Roption (RexprT (tus ++ getUVars ctx) (tvs ++ getVars ctx) iff ==>
                            (RexprT tus tvs iff)))%signature
      (ctxD tus tvs ctx s).
  Proof.
  Abort.

  Lemma Proper_ctxD_impl tus tvs ctx s
  : Proper (Roption (RexprT (tus ++ getUVars ctx) (tvs ++ getVars ctx) Basics.impl ==>
                            (RexprT tus tvs Basics.impl)))%signature
      (ctxD tus tvs ctx s).
  Abort.

  Instance Transitive_CtxMorphism a b c d : Transitive (@CtxMorphism a b c d).
  Proof.
    clear. red. red. intuition.
    specialize (H1 us vs).
    eapply H0. 2: eapply H. 3: eassumption.
    eapply H1. auto.
  Qed.
*)

  Lemma ctxD_SubstMorphism
  : forall tus tvs ctx s s',
      @SubstMorphism tus tvs ctx s s' ->
      forall C C',
      @ctxD tus tvs ctx s = Some C ->
      @ctxD tus tvs ctx s' = Some C' ->
      forall us vs (P : exprT _ _ Prop),
        C' P us vs -> C P us vs.
  Proof.
(*
    induction 1; simpl; intros; forward; inv_all; subst.
    { specialize (IHSubstMorphism _ _ eq_refl eq_refl); eauto. }
    { destruct (ctxD_to_pctxD _ _H5) as [ ? [ ? ? ] ].
      rewrite H6 in *.
      eapply (IHSubstMorphism _ _ H7 H5).
      revert H3.
      eapply H9.
      destruct (ctxD_pctxD_safe _ _ H7).
      rewrite H3 in *.
      generalize (H8 us vs).
      eapply Fmap_pctxD_impl; eauto; try reflexivity.
      clear.
      do 6 red; intros; equivs.
      rewrite _exists_sem.
      rewrite _exists_sem in H2. destruct H2 as [ v ? ]; exists v.
      firstorder. }
    { specialize (IHSubstMorphism _ _ eq_refl eq_refl); eauto. }
    { simpl in *. forward; inv_all; subst.
      intuition. }
*)
  Admitted.

(*
  Lemma rtac_spec_rtac_local_spec
  : forall tus tvs ctx s g r,
      @rtac_spec tus tvs ctx s g r ->
      @rtac_local_spec tus tvs ctx s g r.
  Proof.
    clear.
    unfold rtac_local_spec, rtac_spec.
    destruct r; auto; intros; forward_reason; split; auto.
    { forward.
      destruct (pctxD_to_ctxD _ H2) as [ ? [ ? ? ] ].
      rewrite H4 in *.
      forward.
      destruct (ctxD_to_pctxD _ H3) as [ ? [ ? ? ] ].
      Cases.rewrite_all_goal.
      (** TODO: This seems to be missing things about SubstMorphism **)
  Abort.
*)

  Lemma rtac_spec_rtac_global_spec
  : forall tus tvs ctx s g r,
      @rtac_spec tus tvs ctx s g r ->
      @rtac_global_spec tus tvs ctx s g r.
  Proof.
(*
    clear.
    unfold rtac_local_spec, rtac_spec.
    destruct r; auto; intros; forward_reason; split; auto.
    { forward. inv_all; subst.
      destruct (ctxD_to_pctxD _ H2) as [ ? [ ? ? ] ].
      rewrite H4 in *.
      forward.
      destruct (pctxD_to_ctxD _ H3) as [ ? [ ? ? ] ].
      Cases.rewrite_all_goal.
      destruct H7.
      generalize (@ctxD_SubstMorphism tus tvs ctx s s0 H7 _ _ H2 H8);
        intro; clear H7.
      intros us vs.
      repeat match goal with
               | H : _ |- _ => specialize (H us vs)
             end.
      intros. eapply H11; clear H11.
      eapply H9; [ | eassumption ].
      eauto. }
    { forward. inv_all; subst.
      destruct (ctxD_to_pctxD _ _ H2) as [ ? [ ? ? ] ].
      rewrite H4 in *.
      forward.
      destruct (pctxD_to_ctxD _ _ H3) as [ ? [ ? ? ] ].
      Cases.rewrite_all_goal.
      destruct H6.
      generalize (@ctxD_SubstMorphism tus tvs ctx s s0 H6 _ _ H2 H7);
        intro; clear H7.
      intros us vs.
      repeat match goal with
               | H : _ |- _ => specialize (H us vs)
             end.
      intros. eapply H10; clear H10.
      eapply H8; [ | eassumption ].
      simpl.
      generalize (Proper_pctxD_impl tus tvs ctx s0).
      Cases.rewrite_all_goal.
      intros; inv_all. revert H9. eapply H10; try reflexivity.
      do 6 red. clear.
      intros; equivs; eauto. }
*)
  Admitted.

  Section runOnGoals'.
    Variable tac : rtac (* forall c : Ctx, ctx_subst c -> expr -> Result c *).

    Fixpoint runOnGoals' (tus tvs : tenv typ) (nus nvs : nat)
             (ctx : Ctx) (s : ctx_subst ctx) (g : Goal)
             {struct g}
    : Result ctx :=
      match g with
        | GGoal e => @tac tus tvs nus nvs ctx s e
        | GSolved => Solved s
        | GAll t g =>
          match @runOnGoals' tus (tvs ++ t :: nil) nus (S nvs) (CAll ctx t) (AllSubst s) g with
            | Fail => Fail _
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
            | None => Fail _
            | Some s' =>
              let s' := ExsSubst s s' in
              match @runOnGoals' (tus ++ ts) tvs (length tes + nus) nvs (CExs ctx ts) s' g with
                | Fail => Fail _
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
          match @runOnGoals' tus tvs nus nvs (CHyp ctx h) (HypSubst s) g with
            | Fail => Fail _
            | Solved s => Solved (fromHyp s)
            | More_ s g => More_ (fromHyp s) (GHyp h g)
          end
        | GConj_ l r =>
          match @runOnGoals' tus tvs nus nvs ctx s l with
            | Fail => Fail _
            | Solved s' => @runOnGoals' tus tvs nus nvs ctx s' r
            | More_ s' g' =>
              match @runOnGoals' tus tvs nus nvs ctx s' r with
                | Fail => Fail _
                | Solved s'' => More s'' g'
                | More_ s'' g'' => More s'' (GConj_ g' g'')
              end
          end
      end.

    Definition runOnGoals (tus : tenv typ) (tvs : tenv typ)
               (ctx : Ctx) (s : ctx_subst ctx) (g : Goal)
    : Result ctx :=
      @runOnGoals' tus tvs (length tus + countUVars ctx)
                   (length tvs + countVars ctx) ctx s g.

    Variables tus tvs : tenv typ.
    Hypothesis Htac : rtac_local_sound tus tvs tac.

    Lemma WellFormed_remembers
    : forall a b s s',
        remembers a b s = Some s' ->
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
    Lemma WellFormed_ctx_subst_fromAll : forall t c cs,
                                           @WellFormed_ctx_subst (CAll c t) cs ->
                                           @WellFormed_ctx_subst c (fromAll cs).
    Proof.
    Admitted.
    Lemma WellFormed_ctx_subst_fromHyp : forall t c cs,
                                           @WellFormed_ctx_subst (CHyp c t) cs ->
                                           @WellFormed_ctx_subst c (fromHyp cs).
    Proof.
    Admitted.
    Local Hint Resolve WellFormed_ctx_subst_fromAll WellFormed_ctx_subst_fromHyp.

    Lemma runOnGoals'_sound_ind
    : forall g ctx s,
        @rtac_local_spec tus tvs ctx s g
                        (@runOnGoals' (tus ++ getUVars ctx)
                                      (tvs ++ getVars ctx)
                                      (length tus + countUVars ctx)
                                      (length tvs + countVars ctx)
                                      ctx s g).
    Proof.
      red. induction g; fold runOnGoals' in *.
      { (* All *)
        intros.
        specialize (@IHg (CAll ctx t) (AllSubst s)).
        simpl in *.
(*
        match goal with
          | H : match ?X with _ => _ end |- match match ?Y with _ => _ end with _ => _ end =>
            replace Y with X
        end; [ | f_equal ; omega ].
        destruct (@runOnGoals' (length tus + countUVars ctx)
                               (length tvs + S (countVars ctx)) (CAll ctx t) (AllSubst s) g);
          auto; intros; forward_reason; split; eauto.
        { generalize (@Proper_pctxD_impl tus tvs ctx (fromAll c)).
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
          eauto.  }
        { generalize (@Proper_pctxD_impl tus tvs ctx (fromAll c)).
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
          simpl in *; eauto. } *) admit. }
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
          admit. } }
      { simpl; intros.
        specialize (IHg (CHyp ctx e) s).
(*        match goal with
          | H : match ?X with _ => _ end
            |- match match ?Y with _ => _ end with _ => _ end =>
            replace Y with X; [ remember X as X' ; destruct X' | f_equal ; simpl ; rewrite map_length; omega ]
        end; auto;
        intros; forward_reason; split; eauto; simpl in *;
        unfold subst_pctxD in *; forward; subst; inv_all; subst.
        { destruct H10.
          inversion H1; clear H1; subst. split; auto.
          generalize (Proper_subst_pctxD_impl tus tvs ctx s0).
          simpl.
          rewrite H12 in *; inv_all; subst.
          unfold subst_pctxD.
          Cases.rewrite_all_goal.
          do 3 intro; inv_all.
          eapply H1; [ | reflexivity | reflexivity | eapply H5 ].
          do 6 red.
          intros. eapply equiv_eq_eq in H6; eapply equiv_eq_eq in H8; subst.
          tauto. }
        { destruct H9.
          inversion H1; clear H1; subst. split; auto.
          generalize (Proper_subst_pctxD_impl tus tvs ctx s0).
          simpl.
          rewrite H11 in *. inv_all; subst.
          unfold subst_pctxD.
          Cases.rewrite_all_goal.
          do 3 intro; inv_all.
          eapply H1; [ | reflexivity | reflexivity | eapply H5 ].
          do 6 red.
          intros. eapply equiv_eq_eq in H6; eapply equiv_eq_eq in H8; subst.
          tauto. } *)
       *) admit. }
      { (* Conj *)
(*
        simpl; intros; clear Htac.
        specialize (IHg1 ctx s).
        rename g1 into A.
        rename g2 into B.
        destruct (runOnGoals' (length tus + countUVars ctx) (length tvs + countVars ctx)
                              ctx s A); auto.
        { rename g into A'.
          specialize (IHg2 ctx s0).
          destruct (runOnGoals' (length tus + countUVars ctx) (length tvs + countVars ctx)
                                ctx s0 B); auto.
          { rename g into B'.
            intros; forward_reason; split; auto.
            simpl. forward. forward_reason.
            split; [ etransitivity; eassumption | ].
            intros us vs.
            specialize (H11 us vs).
            specialize (H12 us vs).
            revert H11.
            eapply (Applicative_pctxD _ _ H8).
            eapply pctxD_SubstMorphism.
            3: eassumption. eassumption. eassumption.
            revert H12.
            eapply (Fmap_pctxD_impl _ _ H3); try reflexivity.
            clear. do 6 red.
            intros. equivs. firstorder. }
          { change (rtac_local_spec tus tvs ctx s (GConj_ A B) (More s1 A')).
            eapply Proper_rtac_local_spec; [ reflexivity | eapply More_More_ | ].
            reflexivity. reflexivity.
            simpl.
            intros; forward_reason; split; auto.
            simpl. forward. forward_reason.
            split; [ etransitivity; eassumption | ].
            intros us vs.
            specialize (H11 us vs).
            specialize (H10 us vs).
            revert H10.
            eapply (Applicative_pctxD _ _ H8).
            eapply pctxD_SubstMorphism.
            3: eassumption. eassumption. eassumption.
            revert H11.
            eapply (Fmap_pctxD_impl _ _ H3); try reflexivity.
            clear. do 6 red.
            intros. equivs. firstorder. } *) admit. }
        { (* Hyp *)
(*
          specialize (IHg2 ctx s0).
          destruct (runOnGoals' (length tus + countUVars ctx) (length tvs + countVars ctx)
                                ctx s0 B); auto.
          { rename g into B'.
            intros; forward_reason; split; auto.
            simpl. forward. forward_reason.
            split; [ etransitivity; eassumption | ].
            intros us vs.
            specialize (H10 us vs).
            specialize (H11 us vs).
            revert H10.
            eapply (Applicative_pctxD _ _ H7).
            eapply pctxD_SubstMorphism.
            3: eassumption. eassumption. eassumption.
            revert H11.
            eapply (Fmap_pctxD_impl _ _ H3); try reflexivity.
            clear. do 6 red.
            intros. equivs. firstorder. }
          { intros; forward_reason; split; auto.
            simpl. forward. forward_reason.
            split; [ etransitivity; eassumption | ].
            intros us vs.
            specialize (H9 us vs).
            specialize (H10 us vs).
            revert H9.
            eapply (Applicative_pctxD _ _ H7).
            eapply pctxD_SubstMorphism.
            3: eassumption. eassumption. eassumption.
            revert H10.
            eapply (Fmap_pctxD_impl _ _ H3); try reflexivity.
            clear. do 6 red.
            intros. equivs. firstorder. } } *) admit. }
        
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
        eapply (@Applicative_pctxD tus tvs ctx s); eauto. }
    Qed.

    Theorem runOnGoals_sound ctx s g
    : @rtac_local_spec tus tvs ctx s g
                       (@runOnGoals' (tus ++ getUVars ctx)
                                     (tvs ++ getVars ctx)
                                     (length tus + countUVars ctx)
                                     (length tvs + countVars ctx)
                                     ctx s g).
    Proof.
      eapply runOnGoals'_sound_ind.
    Qed.

  End runOnGoals'.

End parameterized.

Arguments rtac_sound {typ expr subst _ _ _ _ _} tus tvs tac : rename.

Arguments GEx {typ expr} _ _ _ : rename.
Arguments GAll {typ expr} _ _ : rename.
Arguments GHyp {typ expr} _ _ : rename.
Arguments GConj {typ expr} _ _ : rename.
Arguments GConj_ {typ expr} _ _ : rename.
Arguments GConj_list {typ expr} _ : rename.
Arguments GGoal {typ expr} _ : rename.
Arguments GSolved {typ expr} : rename.
Arguments CTop {typ expr} : rename.
Arguments CEx {typ expr} _ _ : rename.
Arguments CAll {typ expr} _ _ : rename.
Arguments CHyp {typ expr} _ _ : rename.

Arguments Fail {typ expr subst _} : rename.
Arguments More {typ expr subst _} _ _ : rename.
Arguments More_ {typ expr subst _} _ _ : rename.
Arguments Solved {typ expr subst _} _ : rename.

Export MirrorCore.ExprI.
Export MirrorCore.SubstI.
Export MirrorCore.ExprDAs.
