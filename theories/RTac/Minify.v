Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Prop.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.Instantiate.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.CoreK.
Require Import MirrorCore.RTac.Reduce.
Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.Util.Nat.


Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.

  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {ExprOk_expr : ExprOk _}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {ExprUVar_expr : ExprUVar expr}.
  Context {ExprUVarOk_expr : ExprUVarOk ExprUVar_expr}.

  Section lookup_compress.
    (** [es] must be pre-translated **)

    Fixpoint lookup_compress (es : list (option expr)) (base u : uvar)
    : expr :=
      match es with
        | nil => (UVar (base + u)) (* DEAD *)
        | e :: es' =>
          match e , u with
            | None , 0 => (UVar base)
            | None , S u => lookup_compress es' (S base) u
            | Some e' , 0 => e'
            | Some _ , S u => lookup_compress es' base u
          end
      end.
  End lookup_compress.

  Definition do_instantiate {c : Ctx typ expr} (cs : ctx_subst c)
             (base : nat) (es : list (option expr)) (u : uvar)
  : option expr :=
    match lt_rem u base with
      | None => (* u < base *)
        ctx_lookup u cs
      | Some u' => Some (lookup_compress es base u')
    end.

  Section minify.
    Variable base : nat.
    Variables (c : Ctx typ expr) (cs : ctx_subst c).

    Fixpoint minify_goal (es : list (option expr))
             (nus : nat)  (g : Goal typ expr)
    : Goal typ expr :=
      match g with
        | GAll t g' =>
          GAll_do_solved t (minify_goal es nus g')
        | GExs ts m g' =>
          let len_ts := length ts in
          let mlist := amap_aslist m nus len_ts in
          let mlist_inst :=
              List.map (Functor.fmap
                          (instantiate (do_instantiate cs base (es ++ mlist))
                                       0)) mlist in
          let tes := combine ts mlist_inst in
          let tes' := filter (fun x => match snd x with
                                         | None => true
                                         | Some _ => false
                                       end) tes in
          let ts' := map fst tes' in
          GExs_nil_check ts' (amap_empty _)
                         (minify_goal (es ++ mlist_inst) (len_ts + nus) g')
        | GHyp e g' =>
          GHyp_do_solved (instantiate (do_instantiate cs base es) 0 e)
                         (minify_goal es nus g')
        | GConj_ g1 g2 =>
          GConj (minify_goal es nus g1) (minify_goal es nus g2)
        | GGoal e =>
          GGoal (instantiate (do_instantiate cs base es) 0 e)
        | GSolved => GSolved
      end.

    Hypothesis base_is_nus : base = length (getUVars c).

    (** TODO: These are all probably redundant **)
    Lemma WellFormed_Goal_GConj
      : forall tus tvs a b,
        WellFormed_Goal (typ:=typ) tus tvs a ->
        WellFormed_Goal tus tvs b ->
        WellFormed_Goal tus tvs (GConj a b).
    Proof.
      destruct a; destruct b; simpl; intros; auto; constructor; auto.
    Qed.

    Lemma WellFormed_Goal_GAll_do_solved
      : forall tus tvs t g,
        WellFormed_Goal tus tvs (GAll t g) ->
        WellFormed_Goal tus tvs (GAll_do_solved t g).
    Proof.
      intros. destruct g; try eassumption.
      do 2 constructor.
    Qed.

    Lemma WellFormed_Goal_GHyp_do_solved
      : forall tus tvs t g,
        WellFormed_Goal tus tvs (GHyp t g) ->
        WellFormed_Goal tus tvs (GHyp_do_solved t g).
    Proof.
      intros. destruct g; try eassumption.
      do 2 constructor.
    Qed.

    (** TODO: I can not capture the meaning of the terms in the list without
     ** their corresponding environments
     **)

    Inductive mapD (_tus _tus' _tvs : tenv typ)
    : forall tus tus' (es : list (option expr)),
        (hlist typD _tus -> hlist typD _tus' -> hlist typD _tvs ->
         hlist typD tus -> hlist typD tus' -> Prop) -> Prop :=
    | MD_nil : forall tus, @mapD _tus _tus' _tvs tus tus nil (fun _ _ _ a b => a = b)
    | MD_None : forall es t tus tus' P,
        @mapD (_tus ++ t :: nil) (_tus' ++ t :: nil) _tvs tus tus' es P ->
        @mapD _tus _tus' _tvs (t :: tus) (t :: tus') (None :: es)
              (fun U U' V a b =>
                    hlist_hd a = hlist_hd b
                 /\ P (hlist_app U (Hcons (hlist_hd a) Hnil))
                      (hlist_app U' (Hcons (hlist_hd a) Hnil)) V
                      (hlist_tl a) (hlist_tl b))
    | MD_Some : forall e es t tus tus' P eD,
        @mapD (_tus ++ t :: nil) _tus' _tvs tus tus' es P ->
        exprD' (_tus' ++ tus') _tvs e t = Some eD ->
        @mapD _tus _tus' _tvs (t :: tus) tus' (Some e :: es)
              (fun U U' V a b =>
                    hlist_hd a = eD (hlist_app U' b) V
                 /\ P (hlist_app U (Hcons (hlist_hd a) Hnil))
                      U' V (hlist_tl a) b).

    Arguments mapD {_ _ _} _ _ _ _.

    (** TODO(gmalecha): move **)
    Lemma nth_error_get_hlist_nth_conv
      : forall T F ls ls' n (pf : ls' = ls),
        @nth_error_get_hlist_nth T F ls n =
        match pf in _ = ls'
              return option { t : T & hlist F ls' -> F t }
        with
          | eq_refl => @nth_error_get_hlist_nth T F ls' n
        end.
    Proof.
      destruct pf; reflexivity.
    Qed.
    (** TODO(gmalecha): move to ExtLib.Data.SigT **)
    Lemma eq_sigT_rw
      : forall T U F (a b : T) (pf : a = b) s,
        match pf in _ = x return @sigT U (F x) with
          | eq_refl => s
        end =
        @existT U (F b) (projT1 s)
                match pf in _ = x return F x (projT1 s) with
                  | eq_refl => (projT2 s)
                end.
    Proof. destruct pf. destruct s; reflexivity. Qed.

    Hint Rewrite eq_sigT_rw : eq_rw.

    Lemma exprD'_UVar_ok
      : forall tus tvs u t get,
        nth_error_get_hlist_nth typD tus u = Some (@existT _ _ t get) ->
        exists eD,
          exprD' tus tvs (UVar u) t = Some eD /\
          forall us vs, get us = eD us vs.
    Proof.
      intros.
      generalize (@UVar_exprD' typ expr _ _ _ _ tus tvs u t).
      destruct (exprD' tus tvs (UVar u) t).
      { intros; forward_reason.
        rewrite H in H0. inv_all. subst. eauto. }
      { eapply nth_error_get_hlist_nth_Some in H. simpl in H.
        forward_reason. destruct 1; try congruence.
        exfalso. clear H. rewrite x in H0.
        forward_reason. inv_all. apply H0. assumption. }
    Qed.

    (** NOTE: This proof is ugly b/c of all of the extraction operations
     **)
    Lemma lookup_compress_sound
    : forall (_tus _tus' tus tus' tvs : list typ)
             (es : list (option expr))
             (R : hlist typD _tus -> hlist typD _tus' ->
                  hlist typD tvs -> hlist typD tus -> hlist typD tus' -> Prop),
        mapD tus tus' es R ->
        forall (u : nat) (t : typ)
               (get : hlist typD (_tus ++ tus) -> typD t),
          nth_error_get_hlist_nth typD (_tus ++ tus) u =
          Some (existT (fun t0 : typ => hlist typD (_tus ++ tus) -> typD t0) t get) ->
          length _tus >= length _tus' ->
          u >= length _tus ->
          exists eUD : exprT (_tus' ++ tus') tvs (typD t),
            exprD' (_tus' ++ tus') tvs
                   (lookup_compress es (length _tus') (u - length _tus)) t =
            Some eUD /\
            (forall _us _us' us us' vs,
                R _us _us' vs us us' ->
                get (hlist_app _us us) = eUD (hlist_app _us' us') vs).
    Proof.
      clear base_is_nus. clear c cs base.
      induction 1.
      { simpl; intros.
        generalize (@UVar_exprD' typ expr _ _ _ _ (_tus' ++ tus) _tvs (length _tus' + (u - length _tus)) t).
        destruct (exprD' (_tus' ++ tus) _tvs (UVar (length _tus' + (u - length _tus))) t).
        { intros; forward_reason.
          eexists; split; eauto.
          eapply nth_error_get_hlist_nth_appR in H; [ | omega ].
          eapply nth_error_get_hlist_nth_appR in H2; [ | omega ].
          simpl in *. forward_reason.
          replace (length _tus' + (u - length _tus) - length _tus')
             with (u - length _tus) in H2 by omega.
          rewrite H in H2. inv_all; subst.
          intros. subst.
          specialize (H5 _us us').
          specialize (H4 _us' us').
          specialize (H3 (hlist_app _us' us') vs).
          rewrite H5; clear H5.
          rewrite <- H4; clear H4.
          eassumption. }
        { intro XXX; exfalso. clear - XXX H H1 H0.
          eapply nth_error_get_hlist_nth_Some in H. simpl in H.
          forward_reason.
          clear H.
          rewrite ListNth.nth_error_app_R in x by omega.
          rewrite ListNth.nth_error_app_R in XXX by omega.
          replace (length _tus' + (u - length _tus) - length _tus')
             with (u - length _tus) in XXX by omega.
          destruct XXX.
          { congruence. }
          { rewrite x in H.
            forward_reason. eapply H2. inv_all. destruct H. apply Rrefl. } } }
      { intros.
        consider (u - length _tus).
        { intros.
          assert (u = length _tus) by omega.
          subst. clear H3 H2.
          simpl.
          generalize (UVar_exprD' (_tus' ++ t :: tus') _tvs (length _tus') t0).
          destruct (exprD' (_tus' ++ t :: tus') _tvs (UVar (length _tus')) t0).
          { intros; forward_reason.
            clear IHmapD.
            eapply nth_error_get_hlist_nth_appR in H2; [ | omega ].
            eapply nth_error_get_hlist_nth_appR in H0; [ | omega ].
            simpl in *. rewrite Minus.minus_diag in *.
            forward_reason; inv_all; subst.
            eexists; split; eauto.
            intros. destruct H0.
            rewrite <- H3; clear H3.
            rewrite H4; clear H4.
            rewrite H5; clear H5.
            subst.
            revert H6. rewrite (UIP_refl x2).
            intros; subst.
            assumption. }
          { clear IHmapD.
            eapply nth_error_get_hlist_nth_Some in H0; forward_reason.
            clear H0.
            intro XXX; exfalso; clear - x XXX; simpl in *.
            repeat rewrite ListNth.nth_error_app_R in * by omega.
            rewrite Minus.minus_diag in *. simpl in *.
            destruct XXX; forward_reason; try congruence. } }
        { intros.
          simpl.
          specialize (IHmapD u).
          repeat rewrite app_length in IHmapD. simpl in IHmapD.
          replace (length _tus' + 1) with (S (length _tus')) in IHmapD by omega.
          replace (u - (length _tus + 1)) with n in IHmapD by omega.
          replace (length _tus + 1) with (S (length _tus)) in IHmapD by omega.
          rewrite nth_error_get_hlist_nth_conv with (pf:=app_ass_trans _tus (t::nil) tus) in H0.
          autorewrite with eq_rw in H0. forward.
          destruct s. specialize (IHmapD _ _ eq_refl).
          destruct IHmapD; [ omega | omega | forward_reason ].
          inv_all; subst.
          rewrite exprD'_conv with (pfu:=app_ass_trans _tus' (t::nil) tus') (pfv:=eq_refl).
          revert H4. autorewrite with eq_rw. simpl.
          intros. inv_all. subst.
          rewrite H5. eexists; split; eauto.
          intros.
          subst.
          destruct H4. eapply H6 in H7.
          revert H7.
          do 2 rewrite hlist_app_assoc.
          autorewrite with eq_rw.
          simpl.
          rewrite (hlist_eta us).
          rewrite (hlist_eta us'). simpl.
          rewrite H4. auto. } }
      { simpl; intros.
        consider (u - length _tus).
        { intros.
          assert (u = length _tus) by omega.
          subst. clear IHmapD H3 H4.
          eapply nth_error_get_hlist_nth_appR in H1; [ | omega ].
          simpl in H1. rewrite Minus.minus_diag in H1.
          forward_reason; inv_all; subst. subst.
          eexists; split; eauto.
          intros; forward_reason.
          rewrite H3; clear H3.
          assumption. }
        { intros.
          rewrite nth_error_get_hlist_nth_conv with (pf:=app_ass_trans _tus (t::nil) tus) in H1.
          autorewrite with eq_rw in H1.
          specialize (IHmapD u).
          forward.
          autorewrite with eq_rw in H5.
          inv_all; subst. subst.
          destruct s; simpl in *.
          destruct (IHmapD _ _ eq_refl); clear IHmapD.
          { rewrite app_length; simpl; omega. }
          { rewrite app_length; simpl; omega. }
          forward_reason.
          rewrite app_length in H5. simpl in *.
          replace (u - (length _tus  + 1)) with n in H5 by omega.
          eexists; split; eauto.
          intros. forward_reason.
          eapply H6 in H8.
          rewrite <- H8; clear H8.
          clear. autorewrite with eq_rw.
          f_equal. rewrite hlist_app_assoc.
          rewrite (hlist_eta us). simpl.
          reflexivity. } }
    Qed.

    Lemma mapD_weaken_tvs : forall _tus _tus' _tvs _tvs' tus tus' es P,
        @mapD _tus _tus' _tvs tus tus' es P ->
        exists P',
          @mapD _tus _tus' (_tvs ++ _tvs') tus tus' es P' /\
          forall U U' V V' a b,
            P U U' V a b <-> P' U U' (hlist_app V V') a b.
    Admitted.

    Hypothesis WF_cs : WellFormed_ctx_subst cs.

    Lemma do_instantiate_sound
      : forall (tus : list typ) (tvs : tenv typ) (tus' : list typ)
               (R : hlist typD (getUVars c) -> hlist typD (getUVars c) ->
                    hlist typD tvs -> hlist typD tus -> hlist typD tus' -> Prop)
               (es : list (option expr)),
        mapD tus tus' es R ->
        forall sD,
          ctx_substD (getUVars c) tvs cs = Some sD ->
        forall (u : nat) (t : typ)
               (get : hlist typD (getUVars c ++ tus) -> typD t),
          nth_error_get_hlist_nth typD (getUVars c ++ tus) u =
          Some
            (existT (fun t0 : typ => hlist typD (getUVars c ++ tus) -> typD t0) t
                    get) ->
          match do_instantiate cs base es u with
            | Some eU =>
              exists eUD : exprT (getUVars c ++ tus') tvs (typD t),
                exprD' (getUVars c ++ tus') tvs eU t = Some eUD /\
                (forall (us : hlist typD (getUVars c ++ tus))
                        (vs : hlist typD tvs) (us' : hlist typD (getUVars c ++ tus'))
                        (vs' : hlist typD tvs),
                    fst (hlist_split (getUVars c) tus us) =
                    fst (hlist_split (getUVars c) tus' us') /\
                    vs = vs' /\
                    R (fst (hlist_split (getUVars c) tus us))
                      (fst (hlist_split (getUVars c) tus us))
                      vs
                      (snd (hlist_split (getUVars c) tus us))
                      (snd (hlist_split (getUVars c) tus' us')) ->
                    sD (fst (hlist_split _ _ us)) vs ->
                    get us = eUD us' vs')
            | None =>
              exists get' : hlist typD (getUVars c ++ tus') -> typD t,
                nth_error_get_hlist_nth typD (getUVars c ++ tus') u =
                Some
                  (existT
                     (fun t0 : typ => hlist typD (getUVars c ++ tus') -> typD t0) t
                     get') /\
                (forall (us : hlist typD (getUVars c ++ tus))
                        (vs : hlist typD tvs) (us' : hlist typD (getUVars c ++ tus'))
                        (vs' : hlist typD tvs),
                    fst (hlist_split (getUVars c) tus us) =
                    fst (hlist_split (getUVars c) tus' us') /\
                    vs = vs' /\
                    R (fst (hlist_split (getUVars c) tus us))
                      (fst (hlist_split (getUVars c) tus us))
                      vs
                      (snd (hlist_split (getUVars c) tus us))
                      (snd (hlist_split (getUVars c) tus' us')) /\
                    sD (fst (hlist_split _ _ us)) vs ->
                    get us = get' us')
          end.
    Proof.
      unfold do_instantiate.
      intros.
      generalize (lt_rem_sound base u).
      destruct (lt_rem u base); intros; forward_reason; subst.
      { destruct (@lookup_compress_sound (getUVars c) (getUVars c) tus tus' tvs es _ H u _ _ H1).
        { Instance Reflexive_ge : Reflexive ge.
          Proof. constructor. Qed.
          reflexivity. }
        { assumption. }
        { forward_reason.
          eexists; split; eauto.
          intros. forward_reason.
          subst.
          eapply H4 in H8.
          repeat rewrite hlist_app_hlist_split in H8.
          rewrite H5 in H8.
          repeat rewrite hlist_app_hlist_split in H8.
          assumption. } }
      { consider (ctx_lookup u cs); intros.
        { generalize (@substD_lookup (ctx_subst c) _ _ _ _ _ _ _ _ _
                                     WF_cs H3 _ _ _ H0);
          intros; forward_reason.
          destruct (@nth_error_get_hlist_nth_appL _ typD tus _ _ H2).
          rewrite H1 in H7. forward_reason; inv_all; subst; simpl in *.
          eapply exprD'_weakenU with (tus':=tus') in H5; try eassumption.
          destruct H5 as [ ? [ ? ? ] ].
          rewrite H4 in H8. inv_all; subst.
          eexists; split; eauto.
          intros. forward_reason. subst.
          specialize (H6 _ _ H10).
          clear - H7 H9 H6 H8.
          specialize (H7 (fst (hlist_split _ _ us)) vs'
                         (snd (hlist_split _ _ us'))).
          specialize (H9 (fst (hlist_split _ _ us)) (snd (hlist_split _ _ us))).
          rewrite hlist_app_hlist_split in H9.
          rewrite H8 in *.
          rewrite hlist_app_hlist_split in H7.
          etransitivity; eauto. etransitivity; eauto. }
        { destruct (@nth_error_get_hlist_nth_appL _ typD tus _ _ H2).
          destruct (@nth_error_get_hlist_nth_appL _ typD tus' _ _ H2).
          forward_reason.
          rewrite H8 in *. rewrite H5. rewrite H1 in *.
          inv_all; subst. destruct x0; simpl in *.
          subst. eexists; split; eauto.
          intros. forward_reason. subst.
          generalize (H9 (fst (hlist_split _ _ us))
                         (snd (hlist_split _ _ us))); clear H9.
          generalize (H7 (fst (hlist_split _ _ us'))
                         (snd (hlist_split _ _ us'))); clear H7.
          repeat rewrite hlist_app_hlist_split.
          rewrite H4. clear.
          intros. rewrite H0. symmetry; eassumption. } }
    Qed.

    Lemma instantiate_do_instantiate_sound
    : forall (tus : list typ) (tvs : tenv typ) (tus' : list typ)
             (e : expr)
             (R : hlist typD (getUVars c) -> hlist typD (getUVars c) ->
                  hlist typD tvs -> hlist typD tus -> hlist typD tus' -> Prop)
             (es : list (option expr)),
        mapD tus tus' es R ->
        forall sD,
          ctx_substD (getUVars c) tvs cs = Some sD ->
        forall gD : exprT (getUVars c ++ tus) tvs Prop,
          propD (getUVars c ++ tus) tvs e = Some gD ->
          exists gD' : exprT (getUVars c ++ tus') tvs Prop,
            propD (getUVars c ++ tus') tvs
                  (instantiate (do_instantiate cs base es) 0 e) =
            Some gD' /\
            (forall (_us : hlist typD (getUVars c)) (_vs : hlist typD tvs)
                    (us : hlist typD tus) (us' : hlist typD tus'),
                R _us _us _vs us us' ->
                sD _us _vs ->
                (gD' (hlist_app _us us') _vs <-> gD (hlist_app _us us) _vs)).
    Proof.
      unfold propD, exprD'_typ0.
      intros; forward; inv_all.
      pose (R':=fun us vs us' vs' =>
                 fst (hlist_split _ _ us) = fst (hlist_split _ _ us') /\
                 vs = vs' /\
                 R (fst (hlist_split _ _ us)) (fst (hlist_split _ _ us)) vs (snd (hlist_split _ _ us)) (snd (hlist_split _ _ us')) /\
                 sD (fst (hlist_split _ _ us)) vs).
      destruct (fun Hu Hv => @expr_subst_sound _ _ _ _ _
                    (do_instantiate cs (length (getUVars c)) es) (fun _ => None) 0 e _ eq_refl
                    nil (getUVars c ++ tus) tvs (getUVars c ++ tus') tvs
                    R'
                    Hu Hv
                    (typ0 (F:=Prop)) _ eq_refl H1).
      { (* Hu *)
        intros.
        generalize (@do_instantiate_sound _ _ _ _ _ H _ H0 _ _ _ H3).
        subst.
        destruct (do_instantiate cs (length (getUVars c)) es u).
        { intros; forward_reason.
          eexists; split; eauto.
          subst R'. simpl. intros.
          forward_reason.
          eapply H4. eauto. eauto. }
        { unfold R'. eauto. } }
      { (* Hv *)
        intros; eexists; split; eauto.
        subst R'. simpl. intros. forward_reason.
        subst. reflexivity. }
      { forward_reason.
        subst. change_rewrite H3.
        eexists; split; eauto.
        intros.
        specialize (H4 (hlist_app _us us) _vs (hlist_app _us us') _vs Hnil).
        subst R'. simpl in H4.
        repeat rewrite hlist_split_hlist_app in H4. simpl in H4.
        autorewrite with eq_rw. rewrite H4.
        reflexivity. eauto. }
    Qed.

    (** TODO(gmalecha): move to bimap **)
    Lemma only_in_range_empty : forall a b,
        only_in_range a b (amap_empty expr).
    Proof.
      clear. red. intros.
      eapply Forall_amap_empty.
    Qed.

    Lemma WellFormed_amap_amap_empty : WellFormed_amap (amap_empty expr).
    Proof. red. eapply FMapSubst.SUBST.WellFormed_empty. Qed.

    Lemma mapD_conv
    : forall a b c us us' vs vs' es es' R
             (pf_us:us=us') (pf_vs:vs=vs'),
        es = es' ->
        (@mapD a b c us vs es R <->
         @mapD a b c us' vs' es'
               match pf_us in _ = us
                   , pf_vs in _ = vs
                     return hlist _ a -> hlist _ b -> hlist _ c ->
                            hlist _ us -> hlist _ vs -> Prop
               with
                 | eq_refl , eq_refl => R
               end).
    Proof.
      clear. destruct pf_us. destruct pf_vs. intros; subst.
      reflexivity.
    Qed.

    (** What is missing here is the fact that [amap_substD a]
     ** is equivalent to [list_substD tus tvs start ls]
     **)
    Theorem amap_substD_list_substD
      : forall tus tvs am (from len : nat) sD maxV,
        WellFormed_bimap from len maxV am ->
        amap_substD tus tvs am = Some sD ->
        exists sD',
          FMapSubst.SUBST.list_substD tus tvs from (amap_aslist am from len) = Some sD' /\
          forall us vs,
            sD us vs <-> sD' us vs.
    Proof.
      destruct 1.
      intros; eapply FMapSubst.SUBST.amap_substD_list_substD; eauto.
      destruct H0. eauto.
    Qed.

    Lemma minify_goal_sound
    : forall g tus tvs tus' es g',
        minify_goal es (length (getUVars c ++ tus)) g = g' ->
        WellFormed_Goal (getUVars c ++ tus) tvs g ->
        WellFormed_Goal (getUVars c ++ tus') tvs g' /\
        forall gD sD R,
          goalD (getUVars c ++ tus) tvs g = Some gD ->
          substD (getUVars c) tvs cs = Some sD ->
          @mapD (getUVars c) (getUVars c) tvs tus tus' es R ->
          exists gD',
            goalD (getUVars c ++ tus') tvs g' = Some gD' /\
            forall _us _vs us us',
              R _us _us _vs us us' ->
              sD _us _vs ->
              (gD' (hlist_app _us us') _vs <->
               gD (hlist_app _us us) _vs).
    Proof.
      induction g.
      { (* All *)
(*
        simpl. intros. inv_all.
        specialize (@IHg tus (tvs ++ t :: nil) tus' es _ _ eq_refl H0
                         (@mapD_weaken_tvs _ _ (t :: nil) _ _ _ _ H1));
          forward_reason.
        destruct (@GAll_do_solved_respects _ _ _ _ _ (getUVars c ++ tus') tvs t
                   _ _ (Reflexive_EqGoal _ _ (minify_goal es (length (getUVars c ++ tus)) g))). *)
(*
        split.
        { subst. eapply H4.
          constructor; assumption. }
        intros; forward; inv_all; subst.
        simpl.
        specialize (H6 _ eq_refl).
        forward_reason; Cases.rewrite_all_goal.
        simpl in H5. rewrite H in H5.
        inversion H5.
        eexists; split; eauto.
        simpl. intros. subst.
        etransitivity. eapply H9. reflexivity. reflexivity.
        eapply forall_iff. intro.
        specialize (H6 _us (hlist_app _vs (Hcons x1 Hnil)) us us').
        rewrite hlist_split_hlist_app in H6. simpl in H6. eauto. *) admit. }
      { (* Exs *)
        cbv beta iota delta [ minify_goal ]; fold minify_goal.
        intros.
        simpl in H.
        remember (amap_aslist a (length (getUVars c ++ tus)) (length l)) as mlist.
        remember (combine l
                   (map
                      (fun x : option expr =>
                       match x with
                       | Some x0 =>
                           Some
                             (instantiate (do_instantiate cs base (es ++ mlist))
                                0 x0)
                       | None => None
                       end) mlist)) as tes.
        remember (map fst
                    (filter
                       (fun x : typ * option expr =>
                          match snd x with
                            | Some _ => false
                            | None => true
                          end) tes)) as ts'.
        remember (map
                    (fun x : option expr =>
                       match x with
                         | Some x0 =>
                           Some
                             (instantiate (do_instantiate cs base (es ++ mlist)) 0
                                          x0)
                         | None => None
                       end) mlist) as mlist_inst.
        rename l into ts.
        inv_all.
        rewrite app_ass in H1.
        specialize (IHg (tus ++ ts) tvs (tus' ++ ts') (es ++ mlist_inst) _
                        eq_refl H1).
        forward_reason.
        destruct (@GExs_nil_check_respects _ _ _ _ _ _
                    (getUVars c ++ tus') tvs ts' (amap_empty expr)
                    (only_in_range_empty _ _)
                    (WellFormed_amap_amap_empty) _ _
                    (Reflexive_EqGoal _ _
                       (minify_goal (es ++ mlist_inst)
                          (length ts + length (getUVars c ++ tus)) g))).
        split.
        { subst g'.
          eapply H4.
          constructor.
          eapply WellFormed_bimap_empty; eauto.
          revert H0. clear.
          repeat rewrite app_length.
          rewrite app_ass.
          match goal with
            | |- ?X -> ?Y => cutrewrite (X = Y); try auto
          end.
          f_equal. f_equal. omega. }
        clear H4.
        rewrite H in *. clear H. (* Can I do this? *)
        simpl in *; intros. forward; inv_all. subst gD.
        rewrite goalD_conv with (pfu:=eq_sym (app_ass_trans _ _ _)) (pfv:=eq_refl) in H.
        autorewrite with eq_rw in H. forward.
        pose (R':=fun U U' V (a : hlist typD (tus ++ ts))
                        (b : hlist typD (tus' ++ ts')) =>
                      R U U' V (fst (hlist_split _ _ a)) (fst (hlist_split _ _ b))
                      /\ e0 (hlist_app (hlist_app U (fst (hlist_split _ _ a)))
                                       (snd (hlist_split _ _ a)))  V).
        assert (exists R'',
                   mapD (tus ++ ts) (tus' ++ ts') (es ++ mlist_inst) R'' /\
                   forall _us _us' _vs a b,
                     R'' _us _us' _vs a b <-> R' _us _us' _vs a b).
        { clear H3 H H5. revert H6.
          revert H7. subst mlist_inst.
          revert Heqmlist. revert H2. subst R'.
          revert Heqts'. subst tes.
          clear. revert e0. revert R.
          revert mlist ts' es. revert tus tvs tus'. revert a.
          induction ts.
          { simpl. intros; subst. simpl in *.
            clear - H6 H7.
            eapply mapD_conv
              with (pf_us:=eq_sym (app_nil_r_trans _))
                   (pf_vs:=eq_sym (app_nil_r_trans _))
                   (es':=es++nil)
              in H6; [ | symmetry; eapply app_nil_r_trans ].
            eexists; split; eauto.
            intros.
            autorewrite with eq_rw.
            rewrite (hlist_eta (snd (hlist_split _ _ a0))).
            rewrite hlist_app_nil_r.
            admit. }
          { admit. } }
(*
        specialize (H3 _ _ R' eq_refl H4 H9).
        forward_reason.
        revert H5.
        rewrite goalD_conv with (pfu:=eq_sym (app_ass_trans _ _ _)) (pfv:=eq_refl). autorewrite with eq_rw.
        revert H3. repeat rewrite app_length.
        replace (length (getUVars c) + (length tus + length ts))
           with (length ts + (length (getUVars c) + length tus)) by omega.
        intro XXX; rewrite XXX.
        inversion 1. eexists; split; eauto.
        intros. do 5 red in H12.
        etransitivity; [ symmetry; eapply H12; reflexivity | ].
*)
        (** TODO(gmalecha): this should work out **)
        admit. (* hard *) }
      { (* Hyp *)
        simpl. intros.
        inv_all.
        specialize (IHg tus tvs tus' es _ eq_refl H0).
        forward_reason.
        split.
        { subst. eapply WellFormed_Goal_GHyp_do_solved.
          constructor. eauto. }
        { intros.
          forwardy. inv_all; subst.
          eapply instantiate_do_instantiate_sound in H3; eauto.
          forward_reason.
          generalize (@GHyp_do_solved_respects typ expr _ _ _ _ _ _ _ H).
          unfold EqGoal; simpl. intros.
          red in H7.
          destruct (H7 (minify_goal es (length (getUVars c ++ tus)) g) (minify_goal es (length (getUVars c ++ tus)) g)); clear H7.
          { clear. split; eauto. reflexivity.
            apply Option.Reflexive_Roption.
            eapply Reflexive_RexprT. eauto with typeclass_instances. }
          revert H9; simpl.
          eapply H2 in H6; clear H2; eauto.
          forward_reason.
          Cases.rewrite_all_goal.
          intros. inversion H9; clear H9; subst.
          eexists; split; eauto.
          intros.
          specialize (H6 _ _ _ _ H9 H10).
          specialize (H3 _ _ _ _ H9 H10).
          rewrite <- H6; clear H6.
          rewrite <- H3; clear H3.
          eapply H11. reflexivity. reflexivity. } }
      { (* Conj *)
        simpl. intros.
        inv_all.
        specialize (@IHg1 tus tvs tus' es _ eq_refl H1).
        specialize (@IHg2 tus tvs tus' es _ eq_refl H2).
        forward_reason.
        split.
        { subst g'. eapply WellFormed_Goal_GConj; assumption. }
        intros.
        forwardy; inv_all.
        subst gD.
        specialize (H3 _ _ _ H9 H7 H8).
        specialize (H5 _ _ _ H6 H7 H8).
        forward_reason.
        subst g'.
        destruct (@GConj_GConj_ typ expr _ _ _ _ (getUVars c ++ tus') tvs
                                (minify_goal es (length (getUVars c ++ tus)) g1)
                                (minify_goal es (length (getUVars c ++ tus)) g1)
                                (Reflexive_EqGoal _ _ _)
                                (minify_goal es (length (getUVars c ++ tus)) g2)
                                (minify_goal es (length (getUVars c ++ tus)) g2)
                                (Reflexive_EqGoal _ _ _)).
        generalize dependent (GConj (minify_goal es (length (getUVars c ++ tus)) g1)
                                    (minify_goal es (length (getUVars c ++ tus)) g2)).
        intro g.
        simpl. Cases.rewrite_all_goal. inversion 2.
        clear base_is_nus.
        subst.
        eexists; split; [ reflexivity | ].
        intros.
        rewrite <- (H10 _ _ _ _ H14 H16).
        rewrite <- (H11 _ _ _ _ H14 H16).
        do 5 red in H15. rewrite H15; [ clear H15 | reflexivity | reflexivity ].
        reflexivity. }
      { (* Goal *)
        intros. clear base_is_nus. subst.
        split.
        { constructor. }
        simpl in *. intros.
        eapply instantiate_do_instantiate_sound; eauto. }
      { (* Solved *)
        intros; clear base_is_nus; subst.
        split; [ constructor | ].
        intros; inv_all; subst.
        simpl. eexists; split; eauto.
        simpl. reflexivity. }
    Qed.

  End minify.

  Definition MINIFY : rtacK typ expr :=
    fun tus tvs nus nvs c cs g =>
      More cs (@minify_goal nus c cs nil nus g).

  Theorem MINIFY_sound : rtacK_sound MINIFY.
    red. unfold MINIFY.
    intros; subst.
    eapply Proper_rtacK_spec;
      [ reflexivity | eapply More_More_; reflexivity | ].
    red.
    intros.
    rewrite <- (app_nil_r_trans (getUVars ctx)) in H.
    destruct (@minify_goal_sound _ _ s eq_refl H0 g nil
                                 (getVars ctx) nil nil _ eq_refl H).
    split; auto.
    split.
    { clear - H1. rewrite app_nil_r_trans in H1. assumption. }
    forward.
    rewrite goalD_conv with (pfu:=app_nil_r_trans _) (pfv:=eq_refl) in H4.
    autorewrite with eq_rw in H4.
    forward.
    destruct (@pctxD_substD  _ _ _ _ _ _ _ _ _ _ H0 H3); forward_reason.
    specialize (H4 _ _ _ eq_refl H6 (@MD_nil _ _ _ _)).
    forward_reason.
    inv_all; subst.
    rewrite goalD_conv with (pfu:=app_nil_r_trans _) (pfv:=eq_refl).
    autorewrite with eq_rw.
    cutrewrite (minify_goal (length (getUVars ctx)) s nil (length (getUVars ctx)) g = minify_goal (length (getUVars ctx)) s nil (length (getUVars ctx ++ nil)) g).
    { rewrite H4.
      split; [ reflexivity | ].
      intros. gather_facts.
      eapply Pure_pctxD; eauto. clear - H8.
      intros. specialize (H8 us vs Hnil Hnil eq_refl H).
      revert H0. autorewrite with eq_rw.
      rewrite <- hlist_app_nil_r. eapply H8. }
    { f_equal. rewrite app_nil_r_trans. reflexivity. }
  Qed.

End parameterized.

(*
Lemma minify_goal_sound
    : forall g tus tvs tus' es g' R,
        (minify_goal es (length (getUVars c ++ tus)) g) = g' ->
        WellFormed_Goal (getUVars c ++ tus) (getVars c ++ tvs) g ->
        @mapD (getUVars c) (getVars c ++ tvs) tus tus' es R ->
        WellFormed_Goal (getUVars c ++ tus') (getVars c ++ tvs) g' /\
        forall gD,
          goalD (getUVars c ++ tus) (getVars c ++ tvs) g = Some gD ->
          exists gD',
            goalD (getUVars c ++ tus') (getVars c ++ tvs) g' = Some gD' /\
            forall _us _vs us us' vs,
              R _us (hlist_app _vs vs) us us' ->
              (gD' (hlist_app _us us') (hlist_app _vs vs) <->
               gD (hlist_app _us us) (hlist_app _vs vs)).
*)