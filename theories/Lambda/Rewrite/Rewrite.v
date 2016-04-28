(** This file implements rewriting using lemmas.
 **)
Require Import Coq.omega.Omega.
Require Import Coq.Classes.Morphisms.
Require Import Coq.PArith.BinPos.
Require Import Coq.Relations.Relations.
Require Import Coq.FSets.FMapPositive.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Pair.
Require Import ExtLib.Recur.Relation.
Require Import ExtLib.Recur.GenRec.
Require Import ExtLib.Recur.Facts.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.VarsToUVars.
Require Import MirrorCore.Instantiate.
Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.Util.Compat.
Require Import MirrorCore.Util.Iteration.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.CoreK.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprTac.
Require Import MirrorCore.Lambda.ExprUnify.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCore.Lambda.ExprSubstitute.
Require Import MirrorCore.Lambda.RewriteRelations.
Require Import MirrorCore.Lambda.Rewrite.Core.

Set Implicit Arguments.
Set Strict Implicit.

Set Suggest Proof Using.

Section setoid.
  Context {typ : Type}.
  Context {func : Type}.
  Context {RType_typD : RType typ}.
  Context {Typ2_Fun : Typ2 RType_typD RFun}.
  Context {RSym_func : RSym func}.

  (** Reasoning principles **)
  Context {RTypeOk_typD : RTypeOk}.
  Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.
  Context {RSymOk_func : RSymOk RSym_func}.
  Context {Typ0_Prop : Typ0 _ Prop}.

  (** TODO(gmalecha): This is not necessary *)
  Context {RelDec_eq_typ : RelDec (@eq typ)}.
  Context {RelDec_Correct_eq_typ : RelDec_Correct RelDec_eq_typ}.

  Local Existing Instance Subst_ctx_subst.
  Local Existing Instance SubstOk_ctx_subst.
  Local Existing Instance SubstUpdate_ctx_subst.
  Local Existing Instance SubstUpdateOk_ctx_subst.
  Local Existing Instance Expr_expr.
  Local Existing Instance ExprOk_expr.

  (* TODO(gmalecha): Wrap all of this up in a type class?
   * Why should it be different than Expr?
   *)
  Variable Rbase : Type.
  Variable Rbase_eq : Rbase -> Rbase -> bool.
  Hypothesis Rbase_eq_ok : forall a b, Rbase_eq a b = true -> a = b.

  Local Notation "'R'" := (R typ Rbase).

  Variable RbaseD : Rbase -> forall t : typ, option (typD t -> typD t -> Prop).

  Hypothesis RbaseD_single_type
  : forall r t1 t2 rD1 rD2,
      RbaseD r t1 = Some rD1 ->
      RbaseD r t2 = Some rD2 ->
      t1 = t2.

  Definition func_sdec (a b : func) : bool :=
    match sym_eqb a b with
    | Some x => x
    | _ => false
    end.

  Definition expr_sdec : expr typ func -> expr typ func -> bool :=
    @expr_eq_sdec typ func _ func_sdec.

  Lemma expr_sdec_sound
  : forall a b : expr typ func, expr_sdec a b = true -> a = b.
  Proof using RSymOk_func RelDec_Correct_eq_typ.
    eapply expr_eq_sdec_ok; eauto.
    unfold func_sdec.
    intros. generalize (sym_eqbOk a b); eauto with typeclass_instances.
    destruct (sym_eqb a b); intros; subst; auto.
    inversion H.
  Qed.

  Section core_rewrite.
    (* This is the implementation of rewriting a single lemma *)

    Require Import MirrorCore.RTac.SolveK.

    (** TODO(gmalecha): This is not a nice interface because it is not
     ** a standard rewriter for two reasons:
     ** 1) It assumes that tvs' = nil, and
     ** 2) It assumes that the relation is the same as the relation for
     **    the lemma.
     **)
    Definition core_rewrite (lem : rw_lemma typ func Rbase)
               (tac : rtacK typ (expr typ func))
    : expr typ func ->
      forall c : Ctx typ (expr typ func),
        ctx_subst c -> option (expr typ func * ctx_subst c) :=
        match typeof_expr nil lem.(vars) lem.(concl).(lhs) with
        | None => fun _ _ _ => None
        | Some t =>
          fun e ctx cs =>
           let ctx' := CExs ctx lem.(vars) in
           let cs' : ctx_subst ctx' := ExsSubst cs (amap_empty _) in
           let (tus,tvs) := getEnvs ctx in
           let nus := length tus in
           let tus' := tus ++ lem.(vars) in
           match
             exprUnify 10 tus' tvs 0 (vars_to_uvars 0 nus lem.(concl).(lhs))
                       e t cs'
           with
           | None => None
           | Some cs'' =>
             let prems :=
                 List.map (fun e => GGoal (vars_to_uvars 0 nus e)) lem.(premises)
             in
             match
               (SOLVEK tac) ctx' cs'' (GConj_list prems)
             with
             | Solved cs''' =>
               match cs''' in ctx_subst ctx
                     return match ctx with
                            | CExs z _ => option (expr typ func * ctx_subst z)
                            | _ => unit
                            end
               with
               | ExsSubst cs'''' sub =>
		 if amap_is_full (length lem.(vars)) sub then
                   let res :=
                       instantiate (fun u => amap_lookup u sub) 0
                                   (vars_to_uvars 0 nus lem.(concl).(rhs))
                   in
                   Some (res, cs'''')
                 else
                   None
               | _ => tt
               end
             | _ => None
             end
           end
        end.

    (** TODO: Move **)
    Lemma lambda_exprD_weakenV
    : forall (tus tvs : tenv typ) (e : expr typ func) (t : typ)
             (val : exprT tus tvs (typD t)) (tvs' : list typ),
        lambda_exprD tus tvs t e = Some val ->
        exists val' : exprT tus (tvs ++ tvs') (typD t),
          lambda_exprD tus (tvs ++ tvs') t e = Some val' /\
          (forall (us : hlist typD tus) (vs : hlist typD tvs)
                  (vs' : hlist typD tvs'),
              val us vs = val' us (hlist_app vs vs')).
    Proof using RSymOk_func RTypeOk_typD Typ2Ok_Fun.
      intros.
      generalize (@exprD_weakenV typ _ (expr typ func) _ _ tus tvs tvs' e t val H).
      eauto.
    Qed.

    (** TODO: Move **)
    Lemma lambda_exprD_weakenU
    : forall (tus tvs : tenv typ) (e : expr typ func) (t : typ)
             (val : exprT tus tvs (typD t)) (tus' : list typ),
        lambda_exprD tus tvs t e = Some val ->
        exists val' : exprT (tus ++ tus') tvs (typD t),
          lambda_exprD (tus ++ tus') tvs t e = Some val' /\
          (forall (us : hlist typD tus) (vs : hlist typD tvs)
                  (us' : hlist typD tus'),
              val us vs = val' (hlist_app us us') vs).
    Proof using RSymOk_func RTypeOk_typD Typ2Ok_Fun.
      intros.
      generalize (@exprD_weakenU typ _ (expr typ func) _ _ tus tus' tvs e t val H).
      eauto.
    Qed.

    Local Instance Subst_amap T : Subst (amap T) T :=
      FMapSubst.SUBST.Subst_subst T.
    Local Instance SubstOk_amap : SubstOk (amap (expr typ func)) typ (expr typ func) :=
      @FMapSubst.SUBST.SubstOk_subst typ _ (expr typ func) _.

    Opaque instantiate.

    Lemma core_rewrite_lemma
    : forall (ctx : Ctx typ (expr typ func)) (t0 : typ)
               (x12 : amap (expr typ func)) (x13 : ctx_subst ctx)
               (l : list typ) (y0 : exprT (getUVars ctx) l (typD t0)),
        WellFormed_entry x13 (length l) x12 ->
        forall (e : expr typ func) (t : tenv typ)
               (y3 : exprT (getUVars ctx ++ l) t Prop)
               (x5 : hlist (fun t1 : typ => exprT (getUVars ctx) t (typD t1)) l),
          amap_substD (getUVars ctx ++ l) t x12 = Some y3 ->
          amap_is_full (length l) x12 = true ->
          (forall (us : hlist typD (getUVars ctx)) (vs : hlist typD t),
              let us' :=
                  hlist_map
                    (fun (t1 : typ) (x : exprT (getUVars ctx) t (typD t1)) => x us vs) x5
              in
              y3 (hlist_app us us') vs) ->
          lambda_exprD (getUVars ctx) l t0 e = Some y0 ->
          exists e'D : exprT (getUVars ctx) t (typD t0),
            lambda_exprD (getUVars ctx) t t0
                   (instantiate (fun u : ExprI.uvar => amap_lookup u x12) 0
                                (vars_to_uvars 0 (length (getUVars ctx)) e)) =
            Some e'D /\
            (forall (us : hlist typD (getUVars ctx)) (vs : hlist typD t),
                e'D us vs =
                y0 us
                   (hlist_map
                      (fun (t1 : typ) (x6 : exprT (getUVars ctx) t (typD t1)) =>
                         x6 us vs) x5)).
    Proof using RType_typD RTypeOk_typD RSymOk_func Typ2Ok_Fun.
      intros ctx t0 x12 x13 l y0 H40 e t y3 x5 Hamap_substD H4 H H13.
      generalize (@vars_to_uvars_sound typ (expr typ func) _ _ _ _ _ _ _ e nil t0 l _ H13).
      destruct 1 as [ ? [ ? ? ] ].
      eapply ExprI.exprD_weakenV with (tvs':=t) in H0; eauto with typeclass_instances.
      destruct H0 as [ ? [ ? ? ] ].
      destruct (@instantiate_sound typ (expr typ func) _ _ _ (getUVars ctx++l) t
                                   (fun u : ExprI.uvar => amap_lookup u x12)
                                   (vars_to_uvars 0 (length (getUVars ctx)) e) nil t0 x0 y3).
      { generalize (@sem_preserves_if_substD (amap (expr typ func)) typ (expr typ func) RType_typD Expr_expr _ _).
        simpl. intro. eapply H3.
        2: eapply Hamap_substD.
        eapply WellFormed_entry_WellFormed_pre_entry in H40.
        destruct H40. assumption. }
      { eassumption. }
      { destruct H3.
        eapply exprD_strengthenU_multi in H3.
        2: eauto with typeclass_instances.
        { destruct H3 as [ ? [ ? ? ] ].
          eexists; split; try eassumption.
          intros.
          specialize (H us vs).
          specialize (H5 _ _ Hnil H).
          simpl in *.
          symmetry.
          etransitivity; [ eapply (H1 _ _ Hnil) | ].
          etransitivity; [ eapply H2 | ].
          etransitivity; [ eapply H5 | ].
          eapply H6. }
        { intros.
          clear H2 H1 H3 H5 H.
          match goal with
          | |- ?X = _ => consider X; try reflexivity; intro
          end.
          exfalso.
          eapply mentionsU_instantiate in H.
          assert (amap_lookup (length (getUVars ctx) + u) x12 <> None).
          { clear - H4 H40 H6.
            destruct H40.
            clear H0.
            red in H.
            destruct H as [ ? [ ? ? ] ].
            clear H H1.
            generalize dependent (length (getUVars ctx)).
            generalize dependent (length l).
            intros.
            eapply pigeon_principle; eauto. }
          destruct H.
          { destruct H. eauto. }
          { destruct H. destruct H. destruct H as [ ? [ ? ? ] ].
            destruct H40.
            consider (amap_lookup (length (getUVars ctx) + u) x12); intros; try congruence.
            eapply FMapSubst.SUBST.normalized_fmapsubst in H1.
            3: eapply H.
            cut (true = false); [ clear; intros; congruence | ].
            rewrite <- H3. rewrite <- H1. reflexivity.
            destruct H5. assumption. } } }
    Qed.

    (* TODO(gmalecha): This is not a nice interface! *)
    Theorem core_rewrite_sound
    : forall ctx (cs : ctx_subst ctx),
        let tus := getUVars ctx in
        let tvs := getVars ctx in
        forall l0 r0 e e' cs',
          WellFormed_rtacK r0 ->
          core_rewrite l0 r0 e cs = Some (e', cs') ->
          WellFormed_ctx_subst cs ->
          WellFormed_ctx_subst cs' /\
          (forall (Hlem : lemmaD (rw_conclD RbaseD) nil nil l0)
                  (Hrtac :           rtacK_sound r0),
           forall (t : typ) (rD : typD t -> typD t -> Prop),
              RD RbaseD (rel (concl l0)) t = Some rD ->
              match pctxD cs with
              | Some _ =>
                match lambda_exprD tus tvs t e with
                | Some eD =>
                  match pctxD cs' with
                  | Some csD' =>
                    match lambda_exprD tus tvs t e' with
                    | Some eD' =>
                      SubstMorphism cs cs' /\
                      (forall (us : hlist typD (getAmbientUVars ctx))
                              (vs : hlist typD (getAmbientVars ctx)),
                          csD'
                            (fun (us0 : hlist typD (getUVars ctx))
                                 (vs0 : hlist typD (getVars ctx)) =>
                               rD (eD us0 vs0) (eD' us0 vs0)) us vs)
                    | None => False
                    end
                  | None => False
                  end
                | None => True
                end
              | None => True
              end).
    Proof using RelDec_Correct_eq_typ RbaseD_single_type
          RTypeOk_typD RSymOk_func Typ2Ok_Fun.
      Opaque vars_to_uvars.
      unfold core_rewrite. generalize dependent 10.
      simpl.
      intros.
      consider (typeof_expr nil l0.(vars) l0.(concl).(lhs)); intros.
      { rewrite getEnvs_getUVars_getVars in *.
        match goal with
        | H : match ?X with _ => _ end = _ |- _ =>
          consider X; intros
        end; try match goal with
                 | H : None = Some _ |- _ => exfalso ; clear - H ; inversion H
                 end.
        assert (WellFormed_rtacK (SOLVEK r0)).
        { apply WF_SOLVEK. assumption. }
        clear H; rename H4 into H.
        match goal with
        | Hrt : WellFormed_rtacK ?X , _ : match ?X ?C ?CS ?G with _ => _ end = _ |- _ =>
          specialize (@Hrt C CS G _ eq_refl)
        end.
        match goal with
        | Hrt : rtacK_spec_wf _ _ ?X , H : match ?Y with _ => _ end = _ |- _ =>
          replace Y with X in H ; [ destruct X eqn:?; intros | f_equal ]
        end; try congruence.
        rewrite (ctx_subst_eta c0) in H3.
        repeat match goal with
               | H : match ?X with _ => _ end = _ |- _ =>
                 let H' := fresh in
                 destruct X eqn:H'; [ | solve [ exfalso; clear - H3; inversion H3 ] ]
               end.
        inv_all. subst.
        destruct (@exprUnify_sound (ctx_subst (CExs ctx (vars l0))) typ func _ _ _ _ _ _ _ _ _ _ n
                                   _ _ _ _ _ _ _ nil H2).
        { constructor; eauto using WellFormed_entry_amap_empty. }
        split.
        { red in H.
          assert (WellFormed_Goal (getUVars (CExs ctx (vars l0)))
                                  (getVars (CExs ctx (vars l0)))
                                  (GConj_list
                                     (map
                                        (fun e : expr typ func =>
                                           GGoal (vars_to_uvars 0 (length (getUVars ctx)) e))
                                        (premises l0)))).
          { eapply WellFormed_Goal_GConj_list. clear.
            induction (premises l0); simpl.
            - constructor.
            - constructor; eauto. constructor. }
          specialize (H H6 H3); clear H6.
          rewrite (ctx_subst_eta c0) in H.
          inv_all. auto. }
        clear H. intro. intro H.
        assert (rtacK_sound (SOLVEK r0)).
        { apply SOLVEK_sound. assumption. }
        clear H; rename H6 into H.
        intros.
        destruct (pctxD cs) eqn:HpctxDcs; trivial.
        destruct (lambda_exprD (getUVars ctx) (getVars ctx) t0 e) eqn:Hlambda_exprDe; trivial.
        simpl in *.
        eapply lemmaD_lemmaD' in Hlem. forward_reason.
        eapply lemmaD'_weakenU with (tus':=getUVars ctx) in H7;
          eauto using ExprOk_expr, rw_concl_weaken.
        simpl in H7. forward_reason.
        unfold lemmaD' in H7.
        forwardy. inv_all. subst.
        unfold rw_conclD in H10.
        forwardy. inv_all; subst.
        assert (t0 = t).
        { revert H0.
          assert (y1 = t0).
          { eapply RD_single_type; eauto. }
          subst t0.
          intro.
          eapply ExprFacts.typeof_expr_weaken with (tus':=getUVars ctx) (tvs':=nil) in H0; eauto.
          simpl in H0. rewrite H10 in H0. inv_all; auto. }
        subst.
        assert (y1 = t).
        { revert H13. revert H6.
          intros. eapply RD_single_type; eauto. }
        subst t. rename y1 into t.
        generalize (fun tus tvs e t => @ExprI.exprD_conv typ _ (expr typ func)
                                          _ tus tus (tvs ++ nil) tvs e t eq_refl
                                          (eq_sym (app_nil_r_trans _))). simpl.
        intro Hlambda_exprD_conv.
        rewrite Hlambda_exprD_conv in H12. autorewrite_with_eq_rw_in H12.
        rewrite Hlambda_exprD_conv in H11. autorewrite_with_eq_rw_in H11.
        forwardy. inv_all. subst.

        generalize (@vars_to_uvars_sound typ (expr typ func) _ _ _ _ _ _ _ _ nil _ _ _ H11).
        simpl. destruct 1 as [ ? [ Hlambda_exprDe_subst ? ] ].
        eapply lambda_exprD_weakenV with (tvs':=getVars ctx) in Hlambda_exprDe_subst; eauto.
        simpl in Hlambda_exprDe_subst. forward_reason.
        intros; subst.
        replace (length (getUVars ctx ++ t :: nil))
           with (S (length (getUVars ctx))) in H15
             by (rewrite app_length; simpl; omega).
        eapply lambda_exprD_weakenU
          with (tus':=l0.(vars)) in Hlambda_exprDe; eauto.
        destruct (drop_exact_append_exact (vars l0) (getUVars ctx)) as [ ? [ Hx ? ] ].
        rewrite Hx in *; clear Hx.
        destruct (pctxD_substD H1 HpctxDcs) as [ ? [ Hx ? ] ].
        rewrite Hx in *; clear Hx.
        destruct Hlambda_exprDe as [ ? [ Hx ? ] ].
        specialize (H5 _ _ _ H15 Hx eq_refl).
        clear Hx.
        forward_reason.
        generalize (pctxD_SubstMorphism_progress H5).
        simpl. rewrite HpctxDcs.
        intro Hx; specialize (Hx _ eq_refl). destruct Hx.
        red in H.
        replace (getUVars ctx ++ vars l0)
           with (getUVars (CExs ctx (vars l0)))
             in Heqr
             by reflexivity.
        eapply (H (CExs ctx (vars l0))) in Heqr. red in Heqr.
        destruct Heqr; eauto.
        { clear. induction (premises l0); simpl. constructor.
          destruct l; simpl. constructor.
          constructor. constructor. eauto. }
        rewrite H22 in *.
        assert (exists Ps,
                   goalD (getUVars ctx ++ vars l0) (getVars ctx)
                         (GConj_list
                            (map
                               (fun e2 : expr typ func =>
                                  GGoal (vars_to_uvars 0 (length (getUVars ctx)) e2))
                               (premises l0))) = Some Ps /\
                   forall (us : hlist typD (getUVars ctx)) us' vs,
                     Ps (hlist_app us us') vs <->
                     Forall (fun y => y us (hlist_app us' Hnil)) y).
        { revert H7.
          destruct l0. simpl in *.
          clear - RTypeOk_typD RSymOk_func Typ2Ok_Fun.
          intros.
          cut (exists Ps : exprT (getUVars ctx ++ vars) (getVars ctx) Prop,
                  goalD (getUVars ctx ++ vars) (getVars ctx)
                        (GConj_list_simple
                           (map
                              (fun e2 : expr typ func =>
                                 GGoal (vars_to_uvars 0 (length (getUVars ctx)) e2))
                              premises)) = Some Ps /\
                  (forall (us : hlist typD (getUVars ctx)) (us' : hlist typD vars)
                          (vs : hlist typD (getVars ctx)),
                      Ps (hlist_app us us') vs <->
                      Forall
                        (fun
                            y0 : hlist typD (getUVars ctx) ->
                                 hlist typD (vars ++ nil) -> Prop =>
                            y0 us (hlist_app us' Hnil)) y)).
          { destruct (goalD_GConj_list_GConj_list_simple
                        (getUVars ctx ++ vars) (getVars ctx)
                        (map (fun e2 : expr typ func =>
                                GGoal (vars_to_uvars 0 (length (getUVars ctx)) e2))
                           premises)).
            { intros; forward_reason; congruence. }
            { intros; forward_reason.
              inv_all. subst. eexists; split; eauto.
              intros.
              rewrite <- H1. eapply H.
              reflexivity. reflexivity. } }
          revert H7. revert y.
          induction premises; simpl; intros.
          { eexists; split; eauto.
            simpl. inv_all. subst.
            split; eauto. }
          { simpl in *.
            forwardy. inv_all. subst.
            unfold exprD_typ0 in H.
            simpl in H. forwardy.
            generalize (@vars_to_uvars_sound typ (expr typ func) _ _ _ _ _ _ _ _ nil _ _ _ H).
            intro. forward_reason.
            unfold propD, exprD_typ0.
            simpl in H2.
            eapply lambda_exprD_weakenV
              with (tvs':=getVars ctx)
                in H2; eauto.
            forward_reason. simpl in H2.
            generalize (@exprD_conv typ _ (expr typ func) _); eauto. simpl.
            intro Hx.
            rewrite Hx
               with (pfu:=f_equal _ (eq_sym (app_nil_r_trans _))) (pfv:=eq_refl)
                 in H2.
            autorewrite_with_eq_rw_in H2.
            forwardy.
            rewrite H2.
            specialize (IHpremises _ H0).
            forward_reason. rewrite H6.
            eexists; split; eauto. simpl.
            intros.
            inv_all. subst.
            intros. rewrite Forall_cons_iff.
            rewrite <- (H7 _ _ vs).
            autorewrite with eq_rw.
            specialize (H3 us (hlist_app us' Hnil) Hnil).
            simpl in *.
            rewrite H3; clear H3.
            erewrite (H4 (hlist_app us (hlist_app us' Hnil)) Hnil vs); clear H4.
            simpl. rewrite hlist_app_nil_r.
            unfold f_equal.
            autorewrite with eq_rw.
            clear.
            generalize (app_nil_r_trans vars).
            generalize dependent (vars ++ nil).
            intros; subst. reflexivity. } }
        destruct H25 as [ ? [ Hx ? ] ].
        change_rewrite Hx in H24; clear Hx.
        forwardy.
        rewrite (ctx_subst_eta c0) in H24.
        simpl in H24.
        forwardy. rewrite H27.
        inv_all; subst.
        destruct (amap_substD_amap_empty (getUVars ctx ++ vars l0)
                                         (getVars ctx)) as [ ? [ Hx ? ] ].
          change_rewrite Hx in H5; clear Hx.
        rewrite HpctxDcs in H5.
        simpl in *.
        destruct (drop_exact_append_exact l0.(vars) (getUVars ctx)) as [ ? [ Hx ? ] ];
          rewrite Hx in *; clear Hx.
        destruct H26.
        inv_all. subst.
        forwardy.
        repeat match goal with
               | H : ?X = _ , H' : ?X = _ |- _ => rewrite H in H'
               end.
        forward_reason; inv_all; subst.
        simpl in *.
        rewrite H5 in *.
        rewrite H3 in *.
        rewrite H27 in *.
        rewrite H24 in *.
        inv_all.
        forwardy.
        generalize H24. intro Hamap_substD.
        eapply subst_getInstantiation in H24;
          eauto using WellFormed_entry_WellFormed_pre_entry
                 with typeclass_instances.
        destruct H24.
        assert (exists e'D,
                   lambda_exprD (getUVars ctx) (getVars ctx) t
                          (instantiate (fun u : ExprI.uvar => amap_lookup u x12)
                                       0 (vars_to_uvars 0 (length (getUVars ctx)) l0.(concl).(rhs))) = Some e'D /\
                   forall us vs,
                     e'D us vs =
                     y0 us (hlist_map
                              (fun (t : typ) (x6 : exprT (getUVars ctx) (getVars ctx) (typD t)) =>
                                 x6 us vs) x5)).
        { eapply core_rewrite_lemma; eauto. }
        destruct H20 as [ ? [ Hx ? ] ]; rewrite Hx; clear Hx.
        split.
        { etransitivity; eassumption. }
        intros.
        eapply pctxD_substD' with (us:=us) (vs:=vs) in H38; eauto with typeclass_instances.
        gather_facts.
        eapply pctxD_SubstMorphism; [ | | eauto | ]; eauto.
        gather_facts.
        eapply pctxD_SubstMorphism; [ | | eauto | ]; eauto.
        gather_facts.
        eapply Pure_pctxD; eauto. intros.
        specialize (H20 us0 vs0).
        specialize (H6 us0 vs0).
        generalize dependent (hlist_map
           (fun (t : typ) (x6 : exprT (getUVars ctx) (getVars ctx) (typD t)) =>
            x6 us0 vs0) x5); simpl; intros.
        rewrite H20; clear H20.
        generalize H6.
        eapply H24 in H6; clear H24.
        specialize (H29 us0 h).
        clear - H19 H16 H14 H17 H25 H28 H21 H9 H18 H22 H23 H26 H6 H8 H29.
        eapply H9 in H8; clear H9.
        rewrite foralls_sem in H8.
        specialize (H8 h).
        setoid_rewrite impls_sem in H8.
        rewrite Quant._forall_sem in H26.
        repeat match goal with
               | H : (forall x : hlist _ _ , _) , H' : hlist _ _ |- _ =>
                 specialize (H H')
               end.
        specialize (H16 (hlist_app us0 h) Hnil vs0).
        specialize (H21 (hlist_app us0 h) vs0).
        rewrite H19; clear H19.
        rewrite H29 in *; clear H29.
        destruct H21; auto.
        specialize (H0 Hnil). simpl in H0.
        rewrite <- H0; clear H0.
        simpl in *.
        rewrite <- H16; clear H16.
        rewrite <- H14; clear H14.
        simpl.
        revert H8.
        instantiate (1:= us0).
        autorewrite_with_eq_rw.
        rewrite hlist_app_nil_r.
        autorewrite_with_eq_rw.
        intros. apply H8; clear H8.
        eapply List.Forall_map.
        eapply H26 in H0; clear H26.
        eapply H25 in H0; clear H25.
        revert H0.
        eapply Forall_impl. clear.
        intros.
        rewrite <- hlist_app_nil_r.
        assumption. }
      { exfalso; clear - H2; inversion H2. }
    Time Qed.

    Theorem core_rewrite_soundX
    : forall ctx (cs : ctx_subst ctx),
        let tus := getUVars ctx in
        let tvs := getVars ctx in
        forall l0 r0 e e' cs'
          (Hlem  : lemmaD (rw_conclD RbaseD) nil nil l0)
          (Hrtac : rtacK_sound r0),
          core_rewrite l0 r0 e cs = Some (e', cs') ->
          WellFormed_ctx_subst cs ->
          WellFormed_ctx_subst cs' /\
          (forall (t : typ) (rD : typD t -> typD t -> Prop),
              RD RbaseD (rel (concl l0)) t = Some rD ->
              match pctxD cs with
              | Some _ =>
                match lambda_exprD tus tvs t e with
                | Some eD =>
                  match pctxD cs' with
                  | Some csD' =>
                    match lambda_exprD tus tvs t e' with
                    | Some eD' =>
                      SubstMorphism cs cs' /\
                      (forall (us : hlist typD (getAmbientUVars ctx))
                              (vs : hlist typD (getAmbientVars ctx)),
                          csD'
                            (fun (us0 : hlist typD (getUVars ctx))
                                 (vs0 : hlist typD (getVars ctx)) =>
                               rD (eD us0 vs0) (eD' us0 vs0)) us vs)
                    | None => False
                    end
                  | None => False
                  end
                | None => True
                end
              | None => True
              end).
    Proof using RelDec_Correct_eq_typ RbaseD_single_type
          RTypeOk_typD RSymOk_func Typ2Ok_Fun.
      Opaque vars_to_uvars.
      intros.
      eapply core_rewrite_sound in H; eauto using rtacK_sound_WellFormed_rtacK.
      forward_reason.
      split; eauto.
    Qed.

  End core_rewrite.

  (* This section implements the re-indexing operation
   * to run [rtac]'s from [mrw]. Note that the main thing to do
   * is extend the context with any extra variables and re-index
   * variables in the term since they are in the opposite order.
   *)
  Section reindexing.
    (* This has to do with converting expressions for tactics *)
    Let _lookupU (u : ExprI.uvar) : option (expr typ func) := None.
    Let _lookupV (under : nat) (above : nat) (v : ExprI.var)
    : option (expr typ func) :=
      Some (Var (if v ?[ ge ] under
                 then v - under
                 else v + above)).

    Definition expr_convert (u : nat) (above : nat)
    : expr typ func -> expr typ func :=
      expr_subst _lookupU (_lookupV u above) 0.

    (** TODO(gmalecha): Move to EnvI or ExtLib.Data.HList **)
    Lemma nth_error_get_hlist_nth_appR'
    : forall T (F : T -> Type) ls u v,
        nth_error_get_hlist_nth F ls u = Some v ->
        forall ls',
        exists v',
          nth_error_get_hlist_nth F (ls' ++ ls) (u + length ls') = Some (existT _ (projT1 v) v') /\
          forall a b,
            projT2 v a = v' (hlist_app b a).
    Proof using.
      induction ls'.
      { simpl.
        replace (u + 0) with u by omega.
        destruct v. eexists; split; eauto.
        simpl. intros.
        rewrite (hlist_eta b). reflexivity. }
      { simpl.
        replace (u + S (length ls')) with (S (u + length ls')) by omega.
        destruct IHls' as [ ? [ ? ? ] ].
        rewrite H0. eexists; split; eauto.
        simpl. intros.
        rewrite (hlist_eta b). simpl. eauto. }
    Qed.

    Lemma expr_convert_sound
    : forall tus tvs tvs' e t eD,
        lambda_exprD tus (tvs ++ tvs') t e = Some eD ->
        exists eD',
          lambda_exprD tus (tvs' ++ tvs) t (expr_convert (length tvs) (length tvs') e) = Some eD' /\
          forall a b c,
            eD a (hlist_app b c) = eD' a (hlist_app c b).
    Proof using RSymOk_func RTypeOk_typD Typ2Ok_Fun.
      unfold expr_convert.
      intros.
      destruct (fun Hu Hv => @ExprI.expr_subst_sound
                    typ _ (expr typ func) Expr_expr _
                    _lookupU
                    (_lookupV (length tvs) (length tvs'))
                    0 e _ eq_refl nil
                    tus (tvs ++ tvs') tus (tvs' ++ tvs)
                    (fun us vs us' vs' =>
                       us = us' /\
                       let (_vs,_vs') := hlist_split _ _ vs in
                       let (__vs,__vs') := hlist_split _ _ vs' in
                       _vs = __vs' /\ _vs' = __vs) Hu Hv t _ eq_refl H).
      { simpl. clear.
        intros. eexists; split; eauto.
        intros. destruct H1; subst; auto. }
      { simpl. intros.
        autorewrite with exprD_rw. simpl.
        consider (u ?[ ge ] length tvs); intros.
        { eapply nth_error_get_hlist_nth_appR in H1; eauto.
          simpl in H1. forward_reason.
          eapply nth_error_get_hlist_nth_weaken with (ls':=tvs) in H1.
          simpl in H1.
          forward_reason. rewrite H1.
          rewrite type_cast_refl; eauto.
          eexists; split; eauto.
          unfold Rcast_val, Rcast, Relim. simpl.
          intros.
          revert H5.
          rewrite <- (hlist_app_hlist_split _ _ vs).
          rewrite <- (hlist_app_hlist_split _ _ vs').
          rewrite hlist_split_hlist_app.
          rewrite hlist_split_hlist_app.
          destruct 1.
          rewrite H3. rewrite <- H4.
          f_equal. tauto. }
        { assert (u < length tvs) by omega.
          eapply nth_error_get_hlist_nth_appL in H3.
          destruct H3. destruct H3.
          rewrite H3 in H1.
          assert (u + length tvs' >= length tvs') by omega.
          destruct H4 as [ ? [ ? ? ] ].
          eapply nth_error_get_hlist_nth_appR' in H4; simpl in H4.
          destruct H4 as [ ? [ ? ? ] ].
          rewrite H4.
          inv_all. subst. simpl.
          rewrite type_cast_refl; eauto.
          eexists; split; eauto.
          intros us vs us' vs'.
          rewrite <- (hlist_app_hlist_split _ _ vs).
          rewrite <- (hlist_app_hlist_split _ _ vs').
          rewrite hlist_split_hlist_app.
          rewrite hlist_split_hlist_app.
          destruct 1.
          simpl in *.
          rewrite H6. rewrite <- H7.
          unfold Rcast_val, Rcast; simpl. f_equal. tauto. } }
      { simpl in H0.
        destruct H0; eexists; split; eauto.
        intros. apply (H1 a (hlist_app b c) a (hlist_app c b) Hnil).
        split; auto.
        do 2 rewrite hlist_split_hlist_app.
        tauto. }
    Qed.

    (* This code starts to build the structure necessary for [rtac]
     *)
    Fixpoint wrap_tvs (tvs : tenv typ) (ctx : Ctx typ (expr typ func))
    : Ctx typ (expr typ func) :=
      match tvs with
      | nil => ctx
      | t :: tvs' => wrap_tvs tvs' (CAll ctx t)
      end.

    Fixpoint wrap_tvs_ctx_subst tvs ctx (cs : ctx_subst ctx)
    : ctx_subst (wrap_tvs tvs ctx) :=
      match tvs as tvs return ctx_subst (wrap_tvs tvs ctx) with
      | nil => cs
      | t :: tvs => wrap_tvs_ctx_subst _ (AllSubst cs)
      end.

    Fixpoint unwrap_tvs_ctx_subst T tvs ctx
    : ctx_subst (wrap_tvs tvs ctx) -> (ctx_subst ctx -> T) -> T :=
      match tvs as tvs
            return ctx_subst (wrap_tvs tvs ctx) -> (ctx_subst ctx -> T) -> T
      with
      | nil => fun cs k => k cs
      | t :: tvs => fun cs k =>
        @unwrap_tvs_ctx_subst T tvs (CAll ctx t) cs (fun z => k (fromAll z))
      end.

    (* TODO(gmalecha): This does not have a stand-alone soundness theorem,
     * which is problematic because it does some quite complex manipulation.
     *)
    Definition for_tactic
               (m : expr typ func ->
                    forall ctx : Ctx typ (expr typ func),
                      ctx_subst ctx -> option (expr typ func * ctx_subst ctx))
    : expr typ func -> mrw typ func (expr typ func) :=
      fun e tvs' ctx cs =>
        let under := length tvs' in
        let nvs := countVars ctx in
        let e' := expr_convert under nvs e in
        match
          m e' _ (@wrap_tvs_ctx_subst tvs' ctx cs)
        with
        | None => None
        | Some (v,cs') =>
          Some (expr_convert nvs under v,
                @unwrap_tvs_ctx_subst _ tvs' ctx cs' (fun x => x))
        end.

    (* TODO(gmalecha): This should go in a new file that implements
     * rewriting databases.
     *)
    Fixpoint using_rewrite_db'
             (ls : list (rw_lemma typ func Rbase * rtacK typ (expr typ func)))
    : expr typ func -> R ->
      forall ctx, ctx_subst ctx -> option (expr typ func * ctx_subst ctx) :=
      match ls with
      | nil => fun _ _ _ _ => None
      | (lem,tac) :: ls =>
        let res := using_rewrite_db' ls in
        let crw := core_rewrite lem tac in
        fun e r ctx cs =>
          if Req_dec Rbase_eq r lem.(concl).(rel) then
            match crw e _ cs with
            | None => res e r ctx cs
            | X => X
            end
          else res e r ctx cs
      end.

    Lemma using_rewrite_db'_sound
    : forall r ctx (cs : ctx_subst ctx),
        let tus := getUVars ctx in
        let tvs := getVars ctx in
        forall hints : list (rw_lemma typ func Rbase * rtacK typ (expr typ func)),
        Forall (fun lt =>
                  lemmaD (rw_conclD RbaseD) nil nil (fst lt) /\
                  rtacK_sound (snd lt)) hints ->
        forall e e' cs',
          @using_rewrite_db' hints e r ctx cs = Some (e', cs') ->
          WellFormed_ctx_subst cs ->
          WellFormed_ctx_subst cs' /\
          (forall (t : typ) (rD : typD t -> typD t -> Prop),
              RD RbaseD r t = Some rD ->
              match pctxD cs with
              | Some _ =>
                match lambda_exprD tus tvs t e with
                | Some eD =>
                  match pctxD cs' with
                  | Some csD' =>
                    match lambda_exprD tus tvs t e' with
                    | Some eD' =>
                      SubstMorphism cs cs' /\
                      (forall (us : hlist typD (getAmbientUVars ctx))
                              (vs : hlist typD (getAmbientVars ctx)),
                          csD'
                            (fun (us0 : hlist typD (getUVars ctx))
                                 (vs0 : hlist typD (getVars ctx)) =>
                                 rD (eD us0 vs0)
                                    (eD' us0 vs0)) us vs)
                    | None => False
                    end
                  | None => False
                  end
                | None => True
                end
              | None => True
              end).
    Proof using RSymOk_func RTypeOk_typD RbaseD_single_type Rbase_eq_ok RelDec_Correct_eq_typ Typ2Ok_Fun.
      induction 1.
      { simpl. inversion 1. }
      { simpl. intros. destruct x.
        assert (using_rewrite_db' l e r cs = Some (e',cs')
             \/ (r = l0.(concl).(rel) /\
                 core_rewrite l0 r0 e cs = Some (e',cs'))).
        { generalize (Req_dec_ok Rbase_eq Rbase_eq_ok r l0.(concl).(rel)).
          destruct (Req_dec Rbase_eq r l0.(concl).(rel)); eauto.
          intros. destruct (core_rewrite l0 r0 e cs); eauto. }
        clear H1. destruct H3; eauto.
        destruct H1. subst. clear IHForall H0.
        simpl in H. destruct H.
        revert H2. revert H3. revert H. revert H0.
        intros.
        eapply core_rewrite_sound in H3; eauto using rtacK_sound_WellFormed_rtacK.
        forward_reason. eauto. }
    Qed.

    Section using_prewrite_db.
      Variable phints : expr typ func -> R -> list (rw_lemma typ func Rbase * rtacK typ (expr typ func)).

      Definition using_prewrite_db' :=
        fun e r => using_rewrite_db' (phints e r) e r.

      Lemma using_prewrite_db_sound'
      : forall r ctx (cs : ctx_subst ctx),
          let tus := getUVars ctx in
          let tvs := getVars ctx in
          forall e e' cs',
            @using_prewrite_db' e r ctx cs = Some (e', cs') ->
            forall (Hrtac_wf : forall e r,
                       Forall (fun lt => WellFormed_rtacK (snd lt)) (phints e r)),
            WellFormed_ctx_subst cs ->
            WellFormed_ctx_subst cs' /\
            ((forall e r tus tvs t eD,
                 lambda_exprD tus tvs t e = Some eD ->
                 Forall (fun lt =>
                           lemmaD (rw_conclD RbaseD) nil nil (fst lt) /\
                           rtacK_sound (snd lt)) (phints e r)) ->
             (forall (t : typ) (rD : typD t -> typD t -> Prop),
                 RD RbaseD r t = Some rD ->
                 match pctxD cs with
                 | Some _ =>
                   match lambda_exprD tus tvs t e with
                   | Some eD =>
                     match pctxD cs' with
                     | Some csD' =>
                       match lambda_exprD tus tvs t e' with
                       | Some eD' =>
                         SubstMorphism cs cs' /\
                         (forall (us : hlist typD (getAmbientUVars ctx))
                                 (vs : hlist typD (getAmbientVars ctx)),
                             csD'
                               (fun (us0 : hlist typD (getUVars ctx))
                                    (vs0 : hlist typD (getVars ctx)) =>
                                  rD (eD us0 vs0)
                                     (eD' us0 vs0)) us vs)
                       | None => False
                       end
                     | None => False
                     end
                   | None => True
                   end
                 | None => True
                 end)).
      Proof using RSymOk_func RTypeOk_typD RbaseD_single_type
            Rbase_eq_ok RelDec_Correct_eq_typ Typ2Ok_Fun.
        simpl.
        unfold using_prewrite_db'.
        intros r ctx cs e. revert cs.
        cut (forall (cs : ctx_subst ctx) (e' : expr typ func) (cs' : ctx_subst ctx),
                using_rewrite_db' (phints e r) e r cs =
                Some (e', cs') ->
                (Forall
                   (fun lt : rw_lemma typ func Rbase * rtacK typ (expr typ func) =>
                      WellFormed_rtacK (snd lt)) (phints e r)) ->
                WellFormed_ctx_subst cs ->
                WellFormed_ctx_subst cs' /\
                ((forall (tus tvs : tenv typ)
                         (t : typ) (eD : exprT tus tvs (typD t)),
                     lambda_exprD tus tvs t e = Some eD ->
                     Forall
                       (fun
                           lt : lemma typ (expr typ func) (rw_concl typ func Rbase) *
                                rtacK typ (expr typ func) =>
                           lemmaD (rw_conclD RbaseD) nil nil (fst lt) /\ rtacK_sound (snd lt))
                       (phints e r)) ->
                 forall (t : typ) (rD : typD t -> typD t -> Prop),
                   RD RbaseD r t = Some rD ->
                   match pctxD cs with
                   | Some _ =>
                     match lambda_exprD (getUVars ctx) (getVars ctx) t e with
                     | Some eD =>
                       match pctxD cs' with
                       | Some csD' =>
                         match lambda_exprD (getUVars ctx) (getVars ctx) t e' with
                         | Some eD' =>
                           SubstMorphism cs cs' /\
                           (forall (us : hlist typD (getAmbientUVars ctx))
                                   (vs : hlist typD (getAmbientVars ctx)),
                               csD'
                                 (fun (us0 : hlist typD (getUVars ctx))
                                      (vs0 : hlist typD (getVars ctx)) =>
                                    rD (eD us0 vs0) (eD' us0 vs0)) us vs)
                         | None => False
                         end
                       | None => False
                       end
                     | None => True
                     end
                   | None => True
                   end)).
        { clear.
          intros; forward_reason.
          eapply H in H0; eauto.
          forward_reason. split; eauto.
          intros.
          eapply H2; eauto. }
        induction (phints e r).
        { inversion 1. }
        { simpl. intros.
          destruct a.
          assert (using_rewrite_db' l e r cs = Some (e',cs')
                  \/ (r = r0.(concl).(rel) /\
                      core_rewrite r0 r1 e cs = Some (e',cs'))).
          { generalize (Req_dec_ok Rbase_eq Rbase_eq_ok r r0.(concl).(rel)).
            destruct (Req_dec Rbase_eq r r0.(concl).(rel)); eauto.
            intros. destruct (core_rewrite r0 r1 e cs); eauto. }
          clear H.
          destruct H2.
          { eapply IHl in H; clear IHl; eauto.
            forward_reason. split; eauto.
            intros. eapply H2; eauto.
            intros. eapply H3 in H5; eauto. inversion H5; eauto.
            inversion H0; auto. }
          { forward_reason. subst.
            split.
            { eapply core_rewrite_sound in H2; eauto.
              forward_reason; eauto.
              inversion H0; trivial. }
            { intros. forward.
              specialize (H _ _ _ _ H5).
              inversion H; clear H; subst; forward_reason.
              eapply core_rewrite_sound in H1; eauto.
              forward_reason; eauto.
              eapply H7 in H3.
              revert H3.
              Cases.rewrite_all_goal.
              trivial.
              inversion H0; trivial. } } }
      Qed.

    End using_prewrite_db.

    Definition using_rewrite_db''
               (ls : list (rw_lemma typ func Rbase * rtacK typ (expr typ func)))
    : expr typ func -> R -> mrw typ func (expr typ func) :=
      let rw_db := using_rewrite_db' ls in
      fun e r => for_tactic (fun e => rw_db e r) e.

    Definition using_prewrite_db''
        (lems : expr typ func -> R -> list (rw_lemma typ func Rbase * rtacK typ (expr typ func)))
    : expr typ func -> R -> mrw typ func (expr typ func) :=
      fun e r =>
        for_tactic (fun e => using_rewrite_db' (lems e r) e r) e.

    Lemma getAmbientUVars_wrap_tvs : forall tvs ctx,
        getAmbientUVars (wrap_tvs tvs ctx) = getAmbientUVars ctx.
    Proof using.
      induction tvs; simpl. reflexivity.
      intros. rewrite IHtvs. reflexivity.
    Defined.

    Lemma getAmbientVars_wrap_tvs : forall tvs ctx,
        getAmbientVars (wrap_tvs tvs ctx) = getAmbientVars ctx.
    Proof using.
      induction tvs; simpl. reflexivity.
      intros. rewrite IHtvs. reflexivity.
    Defined.

    Lemma getVars_wrap_tvs : forall tvs' ctx,
        getVars (wrap_tvs tvs' ctx) = getVars ctx ++ tvs'.
    Proof using.
      induction tvs'; simpl; eauto.
      symmetry. eapply app_nil_r_trans.
      simpl. intros. rewrite IHtvs'. simpl.
      rewrite app_ass_trans. reflexivity.
    Defined.

    Lemma WellFormed_ctx_subst_unwrap_tvs
    : forall tvs' ctx ctx' (cs : ctx_subst _)
             (k : ctx_subst (Ctx_append ctx ctx') -> ctx_subst ctx),
        (forall cs, WellFormed_ctx_subst cs -> WellFormed_ctx_subst (k cs)) ->
        WellFormed_ctx_subst cs ->
        WellFormed_ctx_subst
          (@unwrap_tvs_ctx_subst (ctx_subst ctx) tvs' (Ctx_append ctx ctx') cs k).
    Proof using.
      induction tvs'; simpl; auto.
      intros. specialize (IHtvs' ctx (CAll ctx' a) cs).
      simpl in *. eapply IHtvs'; eauto.
      intros. eapply H. rewrite (ctx_subst_eta cs0) in H1.
      inv_all. assumption.
    Qed.

    Fixpoint unwrap_tvs_ctx_subst' (tvs : tenv typ) (ctx : Ctx typ (expr typ func))
    : ctx_subst (wrap_tvs tvs ctx) -> ctx_subst ctx :=
      match tvs as tvs return ctx_subst (wrap_tvs tvs ctx) -> ctx_subst ctx with
      | nil => fun X => X
      | t :: tvs => fun X => fromAll (unwrap_tvs_ctx_subst' tvs _ X)
      end.

    Theorem unwrap_tvs_ctx_subst_unwrap_tvs_ctx_subst'
    : forall T tvs ctx cs (k : _ -> T),
        k (@unwrap_tvs_ctx_subst' tvs ctx cs) =
        unwrap_tvs_ctx_subst tvs cs k.
    Proof using.
      induction tvs; simpl. auto.
      intros. rewrite <- IHtvs. reflexivity.
    Qed.

    (** TODO: Move **)
    Lemma pctxD_iff : forall ctx (cs : ctx_subst ctx) cD P Q,
        pctxD cs = Some cD ->
        (forall us vs, P us vs <-> Q us vs) ->
        forall us vs,
          cD P us vs <-> cD Q us vs.
    Proof using.
      intros.
      split; eapply Ap_pctxD; eauto; eapply Pure_pctxD; eauto; intros; eapply H0; eauto.
    Qed.

    (** TODO: Move **)
    Lemma forall_hlist_nil : forall T (F : T -> Type) (P : hlist F nil -> Prop),
        (forall x, P x) <-> P Hnil.
    Proof using.
      intros. split. eauto. intros. rewrite hlist_eta. assumption.
    Qed.

    Lemma forall_hlist_cons : forall T (F : T -> Type) t ts (P : hlist F (t :: ts) -> Prop),
        (forall x, P x) <-> (forall x xs, P (Hcons x xs)).
    Proof using.
      intros. split. eauto. intros. rewrite hlist_eta. eapply H.
    Qed.

    Lemma getUVars_wrap_tvs
    : forall tvs' ctx, getUVars (wrap_tvs tvs' ctx) = getUVars ctx.
    Proof using.
      induction tvs'; simpl; auto.
      intros.  rewrite IHtvs'. reflexivity.
    Defined.

    Lemma WellFormed_ctx_subst_wrap_tvs : forall tvs' ctx (cs : ctx_subst ctx),
        WellFormed_ctx_subst cs ->
        WellFormed_ctx_subst (wrap_tvs_ctx_subst tvs' cs).
    Proof using.
      induction tvs'; simpl; auto.
      intros. eapply IHtvs'. constructor. assumption.
    Qed.

    Lemma pctxD_unwrap_tvs_ctx_subst
    : forall tvs ctx (cs : ctx_subst _) cD,
        pctxD cs = Some cD ->
        exists cD',
          pctxD (@unwrap_tvs_ctx_subst _ tvs ctx cs (fun x => x)) = Some cD' /\
          forall (us : hlist typD _) (vs : hlist typD _) (P : exprT _ _ Prop),
            cD' (fun us vs => forall vs', P us (hlist_app vs vs')) us vs <->
            cD match eq_sym (getVars_wrap_tvs tvs ctx) in _ = V
                   , eq_sym (getUVars_wrap_tvs tvs ctx) in _ = U
                     return exprT U V Prop
               with
               | eq_refl , eq_refl => P
               end
               match eq_sym (getAmbientUVars_wrap_tvs tvs ctx) in _ = V
                     return hlist _ V
               with
               | eq_refl => us
               end
               match eq_sym (getAmbientVars_wrap_tvs tvs ctx) in _ = V
                     return hlist _ V
               with
               | eq_refl => vs
               end.
    Proof using RTypeOk_typD RSymOk_func Typ2Ok_Fun.
      intros. rewrite <- unwrap_tvs_ctx_subst_unwrap_tvs_ctx_subst'.
      generalize dependent cD. revert cs. revert ctx.
      induction tvs.
      { simpl. eauto.
        eexists; split; eauto.
        intros.
        eapply pctxD_iff; eauto.
        intros.
        rewrite forall_hlist_nil.
        rewrite hlist_app_nil_r.
        revert vs0.
        refine
          (match app_nil_r_trans (getVars ctx)  as Q in _ = t
                 return forall vs0 : hlist typD _,
               P us0
                 match
                   eq_sym Q in (_ = t) return (hlist typD t)
                 with
                 | eq_refl => vs0
                 end <->
               match
                 eq_sym (eq_sym Q) in (_ = V)
                 return (exprT (getUVars ctx) V Prop)
               with
               | eq_refl => P
               end us0 vs0
           with
           | eq_refl => _
           end).
        reflexivity. }
      { simpl; intros.
        specialize (@IHtvs _ _ _ H).
        forward_reason.
        generalize dependent (unwrap_tvs_ctx_subst' tvs (CAll ctx a) cs).
        intro. rewrite (ctx_subst_eta c); simpl.
        intros; forwardy.
        eexists; split; eauto.
        inv_all. subst. intros.
        specialize (H1 us vs
                       match eq_sym (app_ass_trans (getVars ctx) (a::nil) _) in _ = X
                             return exprT _ X Prop
                       with
                       | eq_refl => P
                       end).
        simpl in *.
        etransitivity; [ etransitivity; [ | eapply H1 ] | ]; clear H1.
        { eapply pctxD_iff; eauto.
          intros.
          rewrite forall_hlist_cons.
          eapply Data.Prop.forall_iff; intros.
          eapply Data.Prop.forall_iff; intros.
          rewrite hlist_app_assoc.
          clear. simpl.
          generalize dependent (app_ass_trans (getVars ctx) (a :: nil) tvs).
          simpl in *.
          generalize dependent ((getVars ctx ++ a :: nil) ++ tvs).
          intros; subst. reflexivity. }
        { clear - H.
          match goal with
          | |- _ _ ?U ?V <-> _ _ ?U' ?V' =>
            replace V with V' ; [ replace U with U' | ]
          end.
          { eapply pctxD_iff; eauto; clear.
            revert P.
            refine
              match app_ass_trans (getVars ctx) (a :: nil) tvs
                    as PF in _ = Z
                    return
                    forall (P : exprT _ Z Prop)
                           (us : hlist typD (getUVars (wrap_tvs tvs (CAll ctx a))))
                           (vs : hlist typD (getVars (wrap_tvs tvs (CAll ctx a)))),
                      match
                        eq_sym (getVars_wrap_tvs tvs (CAll ctx a)) in (_ = V)
                        return (exprT (getUVars (wrap_tvs tvs (CAll ctx a))) V Prop)
                      with
                      | eq_refl =>
                        match
                          eq_sym (getUVars_wrap_tvs tvs (CAll ctx a)) in (_ = U)
                          return (exprT U ((getVars ctx ++ a :: nil) ++ tvs) Prop)
                        with
                        | eq_refl =>
                          match
                            eq_sym PF in (_ = X)
                            return (exprT (getUVars ctx) X Prop)
                          with
                          | eq_refl => P
                          end
                        end
                      end us vs <->
                      match
                        eq_sym
                          (eq_ind_r (fun t : tenv typ => t = Z)
                                    (eq_ind_r (fun l : list typ => l = Z) eq_refl
                                              PF)
                                    (getVars_wrap_tvs tvs (CAll ctx a))) in (_ = V)
                        return (exprT (getUVars (wrap_tvs tvs (CAll ctx a))) V Prop)
                      with
                      | eq_refl =>
                        match
                          eq_sym
                            (eq_ind_r (fun t : tenv typ => t = getUVars ctx) eq_refl
                                      (getUVars_wrap_tvs tvs (CAll ctx a))) in
                          (_ = U) return (exprT U Z Prop)
                        with
                        | eq_refl => P
                        end
                      end us vs
              with
              | eq_refl => _
              end.
            generalize (getVars_wrap_tvs tvs (CAll ctx a)).
            generalize (getUVars_wrap_tvs tvs (CAll ctx a)).
            simpl.
            intros;
            repeat match goal with
               | H : @eq (tenv typ) ?X ?Y |- _ =>
                 first [ generalize dependent X | generalize dependent Y ] ; intros; subst
               | H : @eq (list typ) ?X ?Y |- _ =>
                 first [ generalize dependent X | generalize dependent Y ] ; intros; subst
               end. reflexivity. }
          { clear.
            generalize (getAmbientUVars_wrap_tvs tvs (CAll ctx a)).
            simpl in *. destruct e. reflexivity. }
          { clear.
            generalize (getAmbientVars_wrap_tvs tvs (CAll ctx a)).
            simpl. destruct e. reflexivity. } } }
    Qed.

    Lemma pctxD_wrap_tvs_ctx_subst
    : forall tvs ctx (cs : ctx_subst ctx) cD,
        pctxD cs = Some cD ->
        exists cD',
          pctxD (wrap_tvs_ctx_subst tvs cs) = Some cD' /\
          forall us vs (P : exprT _ _ Prop),
            cD (fun us vs => forall vs', P us (hlist_app vs vs')) us vs <->
            cD' match eq_sym (getVars_wrap_tvs tvs ctx) in _ = V
                                                           , eq_sym (getUVars_wrap_tvs tvs ctx) in _ = U
                      return exprT U V Prop
                with
                | eq_refl , eq_refl => P
                end
                match eq_sym (getAmbientUVars_wrap_tvs tvs ctx) in _ = V
                      return hlist _ V
                with
                | eq_refl => us
                end
                match eq_sym (getAmbientVars_wrap_tvs tvs ctx) in _ = V
                      return hlist _ V
                with
                | eq_refl => vs
                end.
    Proof using.
      induction tvs.
      { simpl. eauto.
        eexists; split; eauto.
        intros; eapply pctxD_iff; eauto.
        intros. rewrite forall_hlist_nil.
        rewrite hlist_app_nil_r. clear.
        autorewrite_with_eq_rw. reflexivity. }
      { simpl. intros.
        specialize (IHtvs (CAll ctx a) (AllSubst cs)).
        simpl in IHtvs. rewrite H in IHtvs.
        specialize (IHtvs _ eq_refl).
        destruct IHtvs as [ ? [ ? ? ] ].
        eexists; split; eauto.
        intros.
        specialize (H1 us vs
                       match eq_sym (app_ass_trans (getVars ctx) (a::nil) _) in _ = X
                             return exprT _ X Prop
                       with
                       | eq_refl => P
                       end).
        etransitivity; [ etransitivity; [ | eapply H1 ] | ]; clear H1.
        { eapply pctxD_iff; eauto.
          intros. rewrite forall_hlist_cons.
          eapply Data.Prop.forall_iff; intro.
          eapply Data.Prop.forall_iff; intro.
          rewrite hlist_app_assoc.
          clear.
          generalize dependent (eq_sym (app_ass_trans (getVars ctx) (a :: nil) tvs)).
          simpl in *. destruct e. reflexivity. }
        { match goal with
          | |- _ _ ?U ?V <-> _ _ ?U' ?V' =>
            replace V with V' ; [ replace U with U' | ]
          end.
          { eapply pctxD_iff; eauto.
            intros.
            generalize (getVars_wrap_tvs tvs (CAll ctx a)).
            generalize (getUVars_wrap_tvs tvs (CAll ctx a)).
            simpl. clear.
            intros;
            repeat match goal with
               | H : @eq (tenv typ) ?X ?Y |- _ =>
                 first [ generalize dependent X | generalize dependent Y ] ; intros; subst
               | H : @eq (list typ) ?X ?Y |- _ =>
                 first [ generalize dependent X | generalize dependent Y ] ; intros; subst
               end. simpl.
            unfold eq_ind_r, eq_ind, eq_rect. simpl.
            autorewrite_with_eq_rw.
            revert vs0. revert P.
            refine
              match app_ass_trans (getVars ctx) (a :: nil) tvs
                    as PF in _ = X
                    return
                    forall P (vs0 : hlist typD ((getVars ctx ++ a :: nil) ++ tvs)),
                      P us0
                        match
                          PF in (_ = x)
                          return (hlist typD x)
                        with
                        | eq_refl => vs0
                        end <->
                      P us0
                        match
                          match
                            eq_sym PF in (_ = y)
                            return (y = X)
                          with
                          | eq_refl => eq_refl
                          end in (_ = x) return (hlist typD x)
                        with
                        | eq_refl => vs0
                        end
              with
              | eq_refl => _
              end.
            reflexivity. }
          { clear.
            generalize (getAmbientUVars_wrap_tvs tvs (CAll ctx a)).
            simpl in *. destruct e. reflexivity. }
          { clear.
            generalize (getAmbientVars_wrap_tvs tvs (CAll ctx a)).
            simpl. destruct e. reflexivity. } } }
    Qed.

    Lemma SubstMorphism_wrap_tvs_ctx_subst
    : forall tvs' ctx cs c,
        SubstMorphism (wrap_tvs_ctx_subst tvs' cs) c ->
        SubstMorphism cs
                      (unwrap_tvs_ctx_subst tvs' c (fun x : ctx_subst ctx => x)).
    Proof using.
      intros.
      rewrite <- unwrap_tvs_ctx_subst_unwrap_tvs_ctx_subst'.
      revert H. revert ctx c cs.
      induction tvs'.
      { simpl. tauto. }
      { simpl. intros.
        eapply IHtvs' in H.
        inv_all. rewrite H. assumption. }
    Qed.

    Definition using_rewrite_db
               (hints : list (rw_lemma typ func Rbase * rtacK typ (expr typ func)))
    : RwAction _ _ _ :=
      fun e r => rw_bind (using_rewrite_db'' hints e r)
                         (fun e => rw_ret (Progress e)).

    Definition rewrite_db_sound hints : Prop :=
      Forall
        (fun
            lt : Lemma.lemma typ (expr typ func) (rw_concl typ func Rbase) *
                 CoreK.rtacK typ (expr typ func) =>
            Lemma.lemmaD (rw_conclD RbaseD) nil nil (fst lt) /\
            CoreK.rtacK_sound (snd lt)) hints.

    Theorem using_rewrite_db_sound
    : forall hints,
        rewrite_db_sound hints ->
        setoid_rewrite_spec RbaseD (using_rewrite_db hints).
    Proof using RSymOk_func RTypeOk_typD RbaseD_single_type
          Rbase_eq_ok RelDec_Correct_eq_typ Typ2Ok_Fun.
      unfold using_rewrite_db, using_rewrite_db''.
      unfold for_tactic.
      red. red. intros.
      unfold rw_bind in H0.
      forwardy. inv_all. subst.
      destruct (fun Hx =>
                    @using_rewrite_db'_sound r _ (wrap_tvs_ctx_subst tvs' cs) hints H
                                             (expr_convert (length tvs') (length (getVars ctx)) e) e1 c0 Hx
                                             (WellFormed_ctx_subst_wrap_tvs _ H1)).
      { rewrite <- H0. f_equal.
        rewrite countVars_getVars. reflexivity. }
      clear H0. subst.
      split.
      { eapply WellFormed_ctx_subst_unwrap_tvs
          with (ctx':=CTop nil nil); eauto. }
      intros.
      specialize (H3 _ _ H0); clear H0.
      destruct (pctxD cs) eqn:HpctxD_cs; trivial.
      destruct (@pctxD_wrap_tvs_ctx_subst tvs' _ _ _ HpctxD_cs) as [ ? [ ? ? ] ].
      rewrite H0 in H3.
      destruct (lambda_exprD (getUVars ctx) (tvs' ++ getVars ctx) t e) eqn:Hlambda_exprD_e; trivial.
      generalize (@exprD_conv typ _ (expr typ func) _). simpl.
      intro Hconv.
      rewrite Hconv
         with (tus':=getUVars ctx) (tvs':=getVars ctx++tvs')
              (pfu:=eq_sym (getUVars_wrap_tvs tvs' ctx)) (pfv:=eq_sym (getVars_wrap_tvs tvs' ctx))
           in H3.
      clear Hconv.
      eapply expr_convert_sound in Hlambda_exprD_e.
      destruct Hlambda_exprD_e as [ ? [ Hx ? ] ].
      rewrite Hx in *; clear Hx.
      autorewrite_with_eq_rw_in H3.
      forwardy.
      destruct (pctxD_unwrap_tvs_ctx_subst _ _ _ H3) as [ ? [ HpctxD_x1 ? ] ].
      rewrite HpctxD_x1.
      generalize (@exprD_conv typ _ (expr typ func) _). simpl.
      intro Hconv.
      rewrite Hconv
         with (pfu:=eq_sym (getUVars_wrap_tvs tvs' ctx)) (pfv:=eq_sym(getVars_wrap_tvs tvs' ctx))
           in H6.
      clear Hconv.
      progress autorewrite_with_eq_rw_in H6.
      forwardy; inv_all; subst.
      eapply expr_convert_sound in H6.
      rewrite <- countVars_getVars in *.
      destruct H6 as [ ? [ Hx ? ] ]; rewrite Hx; clear Hx.
      destruct H7.
      split.
      { clear H9 H8 H4.
        eapply SubstMorphism_wrap_tvs_ctx_subst; eauto. }
      { intros.
        specialize (H9 match
                        eq_sym (getAmbientUVars_wrap_tvs tvs' ctx) in (_ = V)
                        return (hlist typD V)
                      with
                      | eq_refl => us
                      end
                       match
                         eq_sym (getAmbientVars_wrap_tvs tvs' ctx) in (_ = V)
                         return (hlist typD V)
                       with
                       | eq_refl => vs
                       end).
        specialize (H8 us vs
                   (fun us0 vs0 =>
                      rD (x0 us0 vs0) (y2 us0 vs0))).
        simpl in H8.
        generalize dependent (getVars_wrap_tvs tvs' ctx).
        generalize dependent (getUVars_wrap_tvs tvs' ctx).
        generalize dependent (getAmbientUVars_wrap_tvs tvs' ctx).
        generalize dependent (getAmbientVars_wrap_tvs tvs' ctx).
        generalize (Ap_pctxD _ HpctxD_x1).
        generalize (Pure_pctxD _ HpctxD_x1).
        revert H5 H6 H7. clear.
        generalize dependent (getAmbientVars (wrap_tvs tvs' ctx)).
        generalize dependent (getAmbientUVars (wrap_tvs tvs' ctx)).
        generalize dependent (getUVars (wrap_tvs tvs' ctx)).
        generalize dependent (getVars (wrap_tvs tvs' ctx)).
        intros; subst; simpl in *.
        eapply H8 in H9; clear H8.
        revert H9. eapply H0; clear H0.
        eapply H; clear H.
        clear - H5 H6.
        intros. rewrite H5. rewrite <- H6. eauto. }
    Time Qed.

    Definition using_prewrite_db
               (hints : expr typ func -> R ->
                        list (rw_lemma typ func Rbase * rtacK typ (expr typ func)))
    : RwAction _ _ _ :=
      fun e r => rw_bind (using_prewrite_db'' hints e r)
                      (fun e => rw_ret (Progress e)).

    (** TODO(gmalecha): This is almost identical to the above theorem *)
    Theorem using_prewrite_db_sound
    : forall hints : expr typ func -> R ->
                     list (rw_lemma typ func Rbase * rtacK typ (expr typ func)),
        (forall r e,
            Forall (fun lt =>
                      (forall tus tvs t eD,
                          lambda_exprD tus tvs t e = Some eD ->
                          lemmaD (rw_conclD RbaseD) nil nil (fst lt)) /\
                      rtacK_sound (snd lt)) (hints e r)) ->
        setoid_rewrite_spec RbaseD (using_prewrite_db hints).
    Proof using RSymOk_func RTypeOk_typD RbaseD_single_type Rbase_eq_ok
          RelDec_Correct_eq_typ Typ2Ok_Fun.
      intros.
      unfold using_prewrite_db, using_prewrite_db''.
      unfold for_tactic.
      red. red. intros.
      unfold rw_bind in H0.
      forwardy. inv_all. subst.
      destruct (@using_prewrite_db_sound' hints r _ (wrap_tvs_ctx_subst tvs' cs)
                                          (expr_convert (length tvs') (length (getVars ctx)) e) e1 c0).
      { rewrite <- H0.
        unfold using_prewrite_db'.
        rewrite countVars_getVars. reflexivity. }
      { clear - H.
        intros. specialize (H r e).
        revert H.
        eapply Forall_impl. intros. destruct H.
        eauto using rtacK_sound_WellFormed_rtacK. }
      { eauto using WellFormed_ctx_subst_wrap_tvs. }
      clear H0. subst. split.
      { eapply WellFormed_ctx_subst_unwrap_tvs
          with (ctx':=CTop nil nil); eauto. }
      intros.
      specialize (fun Hx => H3 Hx _ _ H0); clear H0.
      destruct (pctxD cs) eqn:HpctxD_cs; trivial.
      destruct (@pctxD_wrap_tvs_ctx_subst tvs' _ _ _ HpctxD_cs) as [ ? [ ? ? ] ].
      rewrite H0 in H3.
      destruct (lambda_exprD (getUVars ctx) (tvs' ++ getVars ctx) t e) eqn:Hlambda_exprD_e; trivial.
      generalize (@exprD_conv typ _ (expr typ func) _). simpl.
      intro Hconv.
      rewrite Hconv
         with (tus':=getUVars ctx) (tvs':=getVars ctx++tvs')
              (pfu:=eq_sym (getUVars_wrap_tvs tvs' ctx)) (pfv:=eq_sym (getVars_wrap_tvs tvs' ctx))
           in H3.
      clear Hconv.
      eapply expr_convert_sound in Hlambda_exprD_e.
      destruct Hlambda_exprD_e as [ ? [ Hx ? ] ].
      rewrite Hx in *; clear Hx.
      autorewrite_with_eq_rw_in H3.
      match goal with
      | H : ?X -> _ |- _ =>
        match type of X with
        | Prop =>
          let H' := fresh in
          assert (H' : X) ; [ clear H | specialize (H H'); clear H' ]
        end
      end.
      { clear - H.
        intros. generalize (H r e).
        eapply Forall_impl. intros; forward_reason.
        split; eauto. }
      forwardy.
      destruct (pctxD_unwrap_tvs_ctx_subst _ _ _ H3) as [ ? [ HpctxD_x1 ? ] ].
      rewrite HpctxD_x1.
      generalize (@exprD_conv typ _ (expr typ func) _). simpl.
      intro Hconv.
      rewrite Hconv
         with (pfu:=eq_sym (getUVars_wrap_tvs tvs' ctx)) (pfv:=eq_sym(getVars_wrap_tvs tvs' ctx))
           in H6.
      clear Hconv.
      autorewrite_with_eq_rw_in H6.
      forwardy; inv_all; subst.
      eapply expr_convert_sound in H6.
      rewrite <- countVars_getVars in *.
      destruct H6 as [ ? [ Hx ? ] ]; rewrite Hx; clear Hx.
      destruct H7.
      split.
      { clear H9 H8 H4.
        eapply SubstMorphism_wrap_tvs_ctx_subst; eauto. }
      { intros.
        specialize (H9 match
                        eq_sym (getAmbientUVars_wrap_tvs tvs' ctx) in (_ = V)
                        return (hlist typD V)
                      with
                      | eq_refl => us
                      end
                       match
                         eq_sym (getAmbientVars_wrap_tvs tvs' ctx) in (_ = V)
                         return (hlist typD V)
                       with
                       | eq_refl => vs
                       end).
        specialize (H8 us vs
                   (fun us0 vs0 =>
                      rD (x0 us0 vs0) (y2 us0 vs0))).
        simpl in H8.
        generalize dependent (getVars_wrap_tvs tvs' ctx).
        generalize dependent (getUVars_wrap_tvs tvs' ctx).
        generalize dependent (getAmbientUVars_wrap_tvs tvs' ctx).
        generalize dependent (getAmbientVars_wrap_tvs tvs' ctx).
        generalize (Ap_pctxD _ HpctxD_x1).
        generalize (Pure_pctxD _ HpctxD_x1).
        revert H5 H6 H7. clear.
        generalize dependent (getAmbientVars (wrap_tvs tvs' ctx)).
        generalize dependent (getAmbientUVars (wrap_tvs tvs' ctx)).
        generalize dependent (getUVars (wrap_tvs tvs' ctx)).
        generalize dependent (getVars (wrap_tvs tvs' ctx)).
        intros; subst; simpl in *.
        eapply H8 in H9; clear H8.
        revert H9. eapply H0; clear H0.
        eapply H; clear H.
        clear - H5 H6.
        intros. rewrite H5. rewrite <- H6. eauto. }
    Qed.

  End reindexing.

End setoid.
