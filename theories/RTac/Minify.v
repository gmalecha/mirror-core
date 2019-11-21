Require Import Coq.omega.Omega.
Require Import ExtLib.Core.RelDec.
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
Require Import MirrorCore.Util.Compat.

Set Implicit Arguments.
Set Strict Implicit.

(** TODO(gmalecha): This should be somewhere **)
Instance Reflexive_ge : Reflexive ge.
Proof. constructor. Qed.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.

  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Expr_expr : Expr typ expr}.
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

  Fixpoint types_after_instantiate (ts : tenv typ) (inst : list (option expr))
  : tenv typ :=
    match ts , inst with
      | nil , nil => nil
      | t :: ts , None :: is => t :: types_after_instantiate ts is
      | t :: ts , Some _ :: is => types_after_instantiate ts is
      | _ , _ => nil
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
          let ts' := types_after_instantiate ts mlist_inst in
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

    (** NOTE: You must have the environments to capture the meaning of
     ** the terms semantically
     **)

    Inductive mapD (_tus _tus' _tus_post' _tvs : tenv typ)
    : forall (tus tus' : tenv typ) (es : list (option expr)),
        (hlist typD _tus -> hlist typD _tus' -> hlist typD _tvs ->
         hlist typD tus -> hlist typD tus' -> hlist typD _tus_post' -> Prop) -> Prop :=
    | MD_nil : @mapD _tus _tus' _tus_post' _tvs nil nil nil (fun _ _ _ a b _ => a = b)
    | MD_None : forall es t tus tus' P,
        @mapD (_tus ++ t :: nil) (_tus' ++ t :: nil) _tus_post' _tvs tus tus' es P ->
        @mapD _tus _tus' _tus_post' _tvs (t :: tus) (t :: tus') (None :: es)
              (fun U U' V a b Upost =>
                    hlist_hd a = hlist_hd b
                 /\ P (hlist_app U (Hcons (hlist_hd a) Hnil))
                      (hlist_app U' (Hcons (hlist_hd a) Hnil)) V
                      (hlist_tl a) (hlist_tl b) Upost)
    | MD_Some : forall e es t tus tus' P eD,
        @mapD (_tus ++ t :: nil) _tus' _tus_post' _tvs tus tus' es P ->
        exprD (_tus' ++ tus' ++ _tus_post') _tvs t e = Some eD ->
        @mapD _tus _tus' _tus_post' _tvs (t :: tus) tus' (Some e :: es)
              (fun U U' V a b Upost =>
                    hlist_hd a = eD (hlist_app U' (hlist_app b Upost)) V
                 /\ P (hlist_app U (Hcons (hlist_hd a) Hnil))
                      U' V (hlist_tl a) b Upost).

    Arguments mapD {_ _ _ _} _ _ _ _.

    Inductive mapD_nil (_tus _tus' _tvs : tenv typ)
    : forall (tus tus' : tenv typ) (es : list (option expr)),
        (hlist typD _tus -> hlist typD _tus' -> hlist typD _tvs ->
         hlist typD tus -> hlist typD tus' -> Prop) -> Prop :=
    | MD_nil_nil : @mapD_nil _tus _tus' _tvs nil nil nil (fun _ _ _ a b => a = b)
    | MD_nil_None : forall es t tus tus' P,
        @mapD_nil (_tus ++ t :: nil) (_tus' ++ t :: nil) _tvs tus tus' es P ->
        @mapD_nil _tus _tus' _tvs (t :: tus) (t :: tus') (None :: es)
              (fun U U' V a b =>
                    hlist_hd a = hlist_hd b
                 /\ P (hlist_app U (Hcons (hlist_hd a) Hnil))
                      (hlist_app U' (Hcons (hlist_hd a) Hnil)) V
                      (hlist_tl a) (hlist_tl b))
    | MD_nil_Some : forall e es t tus tus' P eD,
        @mapD_nil (_tus ++ t :: nil) _tus' _tvs tus tus' es P ->
        exprD (_tus' ++ tus') _tvs t e = Some eD ->
        @mapD_nil _tus _tus' _tvs (t :: tus) tus' (Some e :: es)
              (fun U U' V a b =>
                    hlist_hd a = eD (hlist_app U' b) V
                 /\ P (hlist_app U (Hcons (hlist_hd a) Hnil))
                      U' V (hlist_tl a) b).
    Arguments mapD_nil {_ _ _} _ _ _ _.

    Theorem mapD_mapD_nil
    : forall _tus _tus' _tvs tus tus' es R,
        @mapD _tus _tus' nil _tvs tus tus' es R ->
        exists R',
          @mapD_nil _tus _tus' _tvs tus tus' es R' /\
          forall _us _us' vs us us' us'',
            R _us _us' vs us us' us'' ->
            R' _us _us' vs us us'.
    Proof.
      remember (@nil typ). intros. revert Heql. induction H.
      { eexists; split.
        + constructor.
        + simpl. auto. }
      { intros. specialize (IHmapD Heql).
        forward_reason.
        eexists; split.
        + constructor. eassumption.
        + simpl. intros.
          forward_reason; split; eauto. }
      { intros. specialize (IHmapD Heql).
        subst.
        forward_reason.
        rewrite exprD_conv
          with (pfv:=eq_refl) (pfu:=eq_sym (f_equal _ (app_nil_r_trans _)))
            in H0.
        autorewrite_with_eq_rw_in H0. forwardy; inv_all; subst.
        eexists; split.
        + constructor. eassumption. eassumption.
        + simpl. intros.
          forward_reason; split; eauto.
          rewrite H3; clear H3.
          rewrite (hlist_eta us'').
          rewrite hlist_app_nil_r.
          clear.
          generalize (app_nil_r_trans tus').
          generalize (tus' ++ nil).
          intros; subst. reflexivity. }
    Qed.

    Theorem mapD_nil_mapD
    : forall _tus _tus' _tvs tus tus' es R,
        @mapD_nil _tus _tus' _tvs tus tus' es R ->
        exists R',
          @mapD _tus _tus' nil _tvs tus tus' es R' /\
          forall _us _us' vs us us',
            R _us _us' vs us us' ->
            R' _us _us' vs us us' Hnil.
    Proof.
      induction 1.
      { eexists; split.
        + constructor.
        + simpl. auto. }
      { forward_reason.
        eexists; split.
        + constructor. eassumption.
        + simpl. intros.
          forward_reason; split; eauto. }
      { forward_reason.
        rewrite exprD_conv
          with (pfv:=eq_refl) (pfu:=f_equal _ (app_nil_r_trans _))
            in H0.
        autorewrite_with_eq_rw_in H0. forwardy; inv_all; subst.
        eexists; split.
        + constructor. eassumption. eassumption.
        + simpl. intros.
          forward_reason; split; eauto.
          rewrite H3; clear H3.
          autorewrite_with_eq_rw.
          f_equal.
          rewrite hlist_app_nil_r.
          clear.
          generalize (app_nil_r_trans tus').
          generalize (tus' ++ nil).
          intros; subst. reflexivity. }
    Qed.

    Theorem mapD_nil_mapD_iff
    : forall _tus _tus' _tvs tus tus' es R,
        @mapD_nil _tus _tus' _tvs tus tus' es R ->
        exists R',
          @mapD _tus _tus' nil _tvs tus tus' es R' /\
          forall _us _us' vs us us',
            R _us _us' vs us us' <->
            R' _us _us' vs us us' Hnil.
    Proof.
      induction 1.
      { eexists; split.
        + constructor.
        + simpl. tauto. }
      { forward_reason.
        eexists; split.
        + constructor. eassumption.
        + simpl. intros.
          rewrite H1. tauto. }
      { forward_reason.
        rewrite exprD_conv
          with (pfv:=eq_refl) (pfu:=f_equal _ (app_nil_r_trans _))
            in H0.
        autorewrite_with_eq_rw_in H0. forwardy; inv_all; subst.
        eexists; split.
        + constructor. eassumption. eassumption.
        + simpl. intros.
          rewrite H2; clear H2.
          eapply and_iff; try tauto.
          autorewrite_with_eq_rw.
          rewrite hlist_app_nil_r.
          clear. generalize dependent (app_nil_r_trans tus').
          generalize dependent (tus' ++ nil).
          intros; subst; tauto. }
    Qed.

    Lemma exprD_UVar_ok
    : forall tus tvs u t get,
        nth_error_get_hlist_nth typD tus u = Some (@existT _ _ t get) ->
        exists eD,
          exprD tus tvs t (UVar u) = Some eD /\
          forall us vs, get us = eD us vs.
    Proof.
      intros.
      generalize (@UVar_exprD typ expr _ _ _ _ tus tvs u t).
      destruct (exprD tus tvs t (UVar u)).
      { intros; forward_reason.
        rewrite H in H0. inv_all. subst. eauto. }
      { eapply nth_error_get_hlist_nth_Some in H. simpl in H.
        forward_reason. destruct 1; try congruence.
        exfalso. clear H. rewrite x in H0.
        forward_reason. inv_all. apply H0. assumption. }
    Qed.

    Lemma lookup_compress_app
    : forall xs ys b u,
        lookup_compress (xs ++ ys) b u =
        if u ?[ lt ] length xs then
          lookup_compress xs b u
        else
          lookup_compress ys (b + length (filter (fun x => match x with
                                                           | None => true
                                                           | _ => false
                                                           end) xs)) (u - length xs).
    Proof.
      clear.
      induction xs; simpl.
      { intros; f_equal.
        symmetry; apply Plus.plus_0_r.
        apply Minus.minus_n_O. }
      { intros.
        destruct u; try reflexivity.
        replace (S u ?[ lt ] S (length xs)) with (u ?[ lt ] (length xs)).
        destruct a.
        { rewrite IHxs. forward. }
        { rewrite IHxs. forward.
          f_equal. simpl. omega. }
        { reflexivity. } }
    Qed.

    Lemma nth_error_get_hlist_nth_conv
    : forall (iT : Type) (F : iT -> Type) (ls ls' : list iT) n (pf : ls' = ls),
        nth_error_get_hlist_nth F ls n =
        match pf in _ = ls'
              return option { t : _ & hlist F ls' -> F t }
        with
        | eq_refl => nth_error_get_hlist_nth F ls' n
        end.
    Proof.
      destruct pf; reflexivity.
    Qed.

    (** NOTE: This proof is ugly b/c of all of the extraction operations
     **)
    Lemma lookup_compress_sound
    : forall (_tus _tus' tus tus' tvs : list typ)
             (es : list (option expr))
             (R : hlist typD _tus -> hlist typD _tus' ->
                  hlist typD tvs -> hlist typD tus -> hlist typD tus' -> Prop),
        mapD_nil tus tus' es R ->
        forall (u : nat) (t : typ)
               (get : hlist typD (_tus ++ tus) -> typD t),
          nth_error_get_hlist_nth typD (_tus ++ tus) u =
          Some (existT (fun t0 : typ => hlist typD (_tus ++ tus) -> typD t0) t get) ->
          length _tus >= length _tus' ->
          u >= length _tus ->
          exists eUD : exprT (_tus' ++ tus') tvs (typD t),
            exprD (_tus' ++ tus') tvs t
                  (lookup_compress es (length _tus') (u - length _tus)) =
            Some eUD /\
            (forall _us _us' us us' vs,
                R _us _us' vs us us' ->
                get (hlist_app _us us) = eUD (hlist_app _us' us') vs).
    Proof.
      clear base_is_nus. clear c cs base.
      induction 1.
      { simpl; intros.
        generalize (@UVar_exprD typ expr _ _ _ _ (_tus' ++ nil) _tvs (length _tus' + (u - length _tus)) t).
        destruct (exprD (_tus' ++ nil) _tvs t (UVar (length _tus' + (u - length _tus)))).
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
          generalize (UVar_exprD (_tus' ++ t :: tus') _tvs (length _tus') t0).
          destruct (exprD (_tus' ++ t :: tus') _tvs t0 (UVar (length _tus'))).
          { intros; forward_reason.
            clear IHmapD_nil.
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
          { clear IHmapD_nil.
            eapply nth_error_get_hlist_nth_Some in H0; forward_reason.
            clear H0.
            intro XXX; exfalso; clear - x XXX; simpl in *.
            repeat rewrite ListNth.nth_error_app_R in * by omega.
            rewrite Minus.minus_diag in *. simpl in *.
            destruct XXX; forward_reason; try congruence. } }
        { intros.
          simpl.
          specialize (IHmapD_nil u).
          repeat rewrite app_length in IHmapD_nil. simpl in IHmapD_nil.
          replace (length _tus' + 1) with (S (length _tus')) in IHmapD_nil by omega.
          replace (u - (length _tus + 1)) with n in IHmapD_nil by omega.
          replace (length _tus + 1) with (S (length _tus)) in IHmapD_nil by omega.
          rewrite nth_error_get_hlist_nth_conv with (pf:=app_ass_trans _tus (t::nil) tus) in H0.
          autorewrite_with_eq_rw_in H0. forward.
          destruct s. specialize (IHmapD_nil _ _ eq_refl).
          destruct IHmapD_nil; [ omega | omega | forward_reason ].
          inv_all; subst.
          rewrite exprD_conv with (pfu:=app_ass_trans _tus' (t::nil) tus') (pfv:=eq_refl).
          revert H4. autorewrite_with_eq_rw. simpl.
          unfold tenv.
          generalize (@Data.SigT.eq_sigT_rw _ _ (fun x1 y => hlist (typD (RType:=RType_typ)) x1 -> typD (RType:=RType_typ) y)).
          simpl. intro XXX; rewrite XXX; clear XXX.
          intros. inv_all. subst. simpl in *.
          rewrite H5. eexists; split; eauto.
          intros.
          subst.
          destruct H4. eapply H6 in H7.
          revert H7.
          do 2 rewrite hlist_app_assoc.
          autorewrite_with_eq_rw.
          simpl.
          rewrite (hlist_eta us).
          rewrite (hlist_eta us'). simpl.
          rewrite H4. auto. } }
      { simpl; intros.
        consider (u - length _tus).
        { intros.
          assert (u = length _tus) by omega.
          subst. clear IHmapD_nil H3 H4.
          eapply nth_error_get_hlist_nth_appR in H1; [ | omega ].
          simpl in H1. rewrite Minus.minus_diag in H1.
          forward_reason; inv_all; subst. subst.
          eexists; split; eauto.
          intros; forward_reason.
          rewrite H3; clear H3.
          assumption. }
        { intros.
          rewrite nth_error_get_hlist_nth_conv with (pf:=app_ass_trans _tus (t::nil) tus) in H1.
          autorewrite_with_eq_rw_in H1.
          specialize (IHmapD_nil u).
          forward.
          generalize (@Data.SigT.eq_sigT_rw _ _ (fun x1 y => hlist (typD (RType:=RType_typ)) x1 -> typD (RType:=RType_typ) y)).
          simpl. intro XXX; rewrite XXX in H5; clear XXX.
          autorewrite_with_eq_rw_in H5.
          inv_all; subst. subst.
          destruct s; simpl in *.
          destruct (IHmapD_nil _ _ eq_refl); clear IHmapD_nil.
          { rewrite app_length; simpl; omega. }
          { rewrite app_length; simpl; omega. }
          forward_reason.
          rewrite app_length in H5. simpl in *.
          replace (u - (length _tus  + 1)) with n in H5 by omega.
          eexists; split; eauto.
          intros. forward_reason.
          eapply H6 in H8.
          rewrite <- H8; clear H8.
          clear. autorewrite_with_eq_rw.
          f_equal. rewrite hlist_app_assoc.
          rewrite (hlist_eta us). simpl.
          reflexivity. } }
    Qed.

    Lemma mapD_weaken_post
    : forall _tus _tus' _tus_post _tus_post' _tvs tus tus' es P,
        @mapD _tus _tus' _tus_post _tvs tus tus' es P ->
        exists P',
          @mapD _tus _tus' (_tus_post ++ _tus_post') _tvs tus tus' es P' /\
          forall U U' c d V a b,
            P U U' V a b c <-> P' U U' V a b (hlist_app c d).
    Proof.
      induction 1.
      { eexists. split. econstructor. simpl. reflexivity. }
      { forward_reason.
        eexists; split. econstructor. eassumption.
        simpl. intros.
        rewrite H1. reflexivity. }
      { forward_reason.
        eapply exprD_weaken with (tus':=_tus_post') (tvs' := nil) in H0;
          eauto with typeclass_instances.
        forward_reason.
        rewrite exprD_conv
           with (pfv:=eq_refl) (pfu:=eq_sym (app_ass_trans _ _ _)) in H0.
        rewrite exprD_conv
           with (pfv:=eq_sym (app_nil_r_trans _)) (pfu:=f_equal _ (eq_sym (app_ass_trans _ _ _))) in H0.
        autorewrite_with_eq_rw_in H0.
        forwardy.
        eexists; split. econstructor. eassumption.
        eassumption. simpl. intros.
        rewrite H2. inv_all. subst.
        instantiate (1:=d).
        erewrite H3 with (vs':=Hnil) (us':=d).
        apply and_iff; [ | reflexivity ].
        autorewrite_with_eq_rw.
        rewrite hlist_app_assoc.
        autorewrite_with_eq_rw.
        rewrite hlist_app_nil_r.
        autorewrite_with_eq_rw.
        rewrite hlist_app_assoc.
        generalize (hlist_app b (hlist_app c0 d)).
        destruct (app_ass_trans tus' _tus_post'0 _tus_post').
        reflexivity. }
    Qed.

    Lemma mapD_weaken_tvs
    : forall _tus _tus' _tus_post _tvs _tvs' tus tus' es P,
        @mapD _tus _tus' _tus_post _tvs tus tus' es P ->
        exists P',
          @mapD _tus _tus' _tus_post (_tvs ++ _tvs') tus tus' es P' /\
          forall U U' c V V' a b,
            P U U' V a b c <-> P' U U' (hlist_app V V') a b c.
    Proof.
      induction 1; simpl; intros.
      { eexists. split. constructor.
        simpl. intros; tauto. }
      { forward_reason.
        eexists; split.
        - econstructor. eauto.
        - simpl. intros. rewrite H1. reflexivity. }
      { eapply exprD_weakenV with (tvs':=_tvs') in H0; eauto.
        forward_reason.
        eexists; split.
        - econstructor; eauto.
        - simpl. intros.
          rewrite <- H2. rewrite <- H3. reflexivity. }
    Qed.

    Hypothesis WF_cs : WellFormed_ctx_subst cs.

    Lemma do_instantiate_sound
      : forall (tus tvs tus' : tenv typ)
               (R : hlist typD (getUVars c) -> hlist typD (getUVars c) ->
                    hlist typD (getVars c ++ tvs) -> hlist typD tus ->
                    hlist typD tus' -> Prop)
               (es : list (option expr)),
        @mapD_nil (getUVars c) (getUVars c) (getVars c ++ tvs) tus tus' es R ->
        forall sD,
          ctx_substD (getUVars c) (getVars c) cs = Some sD ->
        forall (u : nat) (t : typ)
               (get : hlist typD (getUVars c ++ tus) -> typD t),
          nth_error_get_hlist_nth typD (getUVars c ++ tus) u =
          Some
            (existT (fun t0 : typ => hlist typD (getUVars c ++ tus) -> typD t0) t
                    get) ->
          match do_instantiate cs base es u with
            | Some eU =>
              exists eUD : exprT (getUVars c ++ tus') (_ ++ tvs) (typD t),
                exprD (getUVars c ++ tus') (getVars c ++ tvs) t eU = Some eUD /\
                (forall (us : hlist typD (getUVars c ++ tus))
                        _vs (vs : hlist typD tvs) (us' : hlist typD (getUVars c ++ tus'))
                        (vs' : hlist typD tvs),
                    fst (hlist_split (getUVars c) tus us) =
                    fst (hlist_split (getUVars c) tus' us') /\
                    vs = vs' /\
                    R (fst (hlist_split (getUVars c) tus us))
                      (fst (hlist_split (getUVars c) tus us))
                      (hlist_app _vs vs)
                      (snd (hlist_split (getUVars c) tus us))
                      (snd (hlist_split (getUVars c) tus' us')) ->
                    sD (fst (hlist_split _ _ us)) _vs ->
                    get us = eUD us' (hlist_app _vs vs'))
            | None =>
              exists get' : hlist typD (getUVars c ++ tus') -> typD t,
                nth_error_get_hlist_nth typD (getUVars c ++ tus') u =
                Some
                  (existT
                     (fun t0 : typ => hlist typD (getUVars c ++ tus') -> typD t0) t
                     get') /\
                (forall (us : hlist typD (getUVars c ++ tus))
                        _vs (vs : hlist typD tvs) (us' : hlist typD (getUVars c ++ tus'))
                        (vs' : hlist typD tvs),
                    fst (hlist_split (getUVars c) tus us) =
                    fst (hlist_split (getUVars c) tus' us') /\
                    vs = vs' /\
                    R (fst (hlist_split (getUVars c) tus us))
                      (fst (hlist_split (getUVars c) tus us))
                      (hlist_app _vs vs)
                      (snd (hlist_split (getUVars c) tus us))
                      (snd (hlist_split (getUVars c) tus' us')) /\
                    sD (fst (hlist_split _ _ us)) _vs ->
                    get us = get' us')
          end.
    Proof using (ExprOk_expr ExprUVarOk_expr RTypeOk_typ WF_cs base_is_nus).
      unfold do_instantiate.
      intros.
      generalize (lt_rem_sound base u).
      destruct (lt_rem u base); intros; forward_reason; subst.
      { destruct (@lookup_compress_sound (getUVars c) (getUVars c) tus tus' (_ ++ tvs) es _ H u _ _ H1).
        { reflexivity. }
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
          eapply exprD_weaken with (tus':=tus') (tvs':=tvs) in H5; try eassumption.
          destruct H5 as [ ? [ ? ? ] ].
          rewrite H4 in H8. inv_all; subst.
          eexists; split; eauto.
          intros. forward_reason. subst.
          specialize (H6 _ _ H10).
          clear - H7 H9 H6 H8.
          specialize (H7 (fst (hlist_split _ _ us)) _vs
                         (snd (hlist_split _ _ us')) vs').
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

    Lemma instantiate_do_instantiate_exprD_sound
    : forall (tus : list typ) (tvs : tenv typ) (tus' : list typ)
             (e : expr) t
             (R : hlist typD (getUVars c) -> hlist typD (getUVars c) ->
                  hlist typD _ -> hlist typD tus -> hlist typD tus' -> Prop)
             (es : list (option expr)),
        @mapD_nil (getUVars c) (getUVars c) (getVars c ++ tvs) tus tus' es R ->
        forall sD,
          ctx_substD (getUVars c) (getVars c) cs = Some sD ->
        forall gD : exprT (getUVars c ++ tus) _ _,
          exprD (getUVars c ++ tus) (getVars c ++ tvs) t e = Some gD ->
          exists gD' : exprT (getUVars c ++ tus') (getVars c ++ tvs) _,
            exprD (getUVars c ++ tus') (getVars c ++ tvs) t
                  (instantiate (do_instantiate cs base es) 0 e) =
            Some gD' /\
            (forall (_us : hlist typD (getUVars c)) _vsx (_vs : hlist typD tvs)
                    (us : hlist typD tus) (us' : hlist typD tus'),
                R _us _us (hlist_app _vsx _vs) us us' ->
                sD _us _vsx ->
                (gD' (hlist_app _us us') (hlist_app _vsx _vs) =
                 gD (hlist_app _us us) (hlist_app _vsx _vs))).
    Proof.
      intros; forward; inv_all.
      pose (R':=fun (us : hlist _ (getUVars c ++ tus)) (vs : hlist _ (getVars c ++ tvs))
                    (us' : hlist _ (getUVars c ++ tus')) (vs' : hlist _ (getVars c ++ tvs)) =>
                 fst (hlist_split _ _ us) = fst (hlist_split _ _ us') /\
                 vs = vs' /\
                 R (fst (hlist_split _ _ us)) (fst (hlist_split _ _ us)) vs (snd (hlist_split _ _ us)) (snd (hlist_split _ _ us')) /\
                 sD (fst (hlist_split _ _ us)) (fst (hlist_split _ _ vs))).
      destruct (fun Hu Hv => @expr_subst_sound _ _ _ _ _
                    (do_instantiate cs (length (getUVars c)) es) (fun _ => None) _ e _ eq_refl
                    nil (getUVars c ++ tus) (getVars c ++ tvs) (getUVars c ++ tus') (getVars c ++ tvs)
                    R'
                    Hu Hv
                    t _ eq_refl H1).
      { (* Hu *)
        intros.
        generalize (@do_instantiate_sound _ _ _ _ _ H _ H0 _ _ _ H3).
        subst.
        destruct (do_instantiate cs (length (getUVars c)) es u).
        { intros; forward_reason.
          eexists; split; eauto.
          subst R'. simpl. intros.
          forward_reason.
          rewrite <- (hlist_app_hlist_split _ _ vs').
          eapply H5.
          split; eauto. split; eauto.
          rewrite hlist_app_hlist_split. subst. auto.
          subst. auto. }
        { unfold R'.
          clear. destruct 1.
          exists x.
          forward_reason; split; eauto.
          intros. forward_reason. eapply H0.
          split. eassumption.
          split.
          2: split; try eassumption.
          2: rewrite hlist_app_hlist_split; eassumption.
          reflexivity. } }
      { (* Hv *)
        intros; eexists; split; eauto.
        subst R'. simpl. intros. forward_reason.
        subst. reflexivity. }
      { forward_reason.
        subst. change_rewrite H2.
        eexists; split; eauto.
        intros.
        specialize (H3 (hlist_app _us us) (hlist_app _vsx _vs) (hlist_app _us us') (hlist_app _vsx _vs) Hnil).
        subst R'. simpl in H3.
        repeat rewrite hlist_split_hlist_app in H3. simpl in H3.
        autorewrite_with_eq_rw. rewrite H3.
        reflexivity. eauto. }
    Qed.

    Corollary instantiate_do_instantiate_propD_sound
    : forall (tus : list typ) (tvs : tenv typ) (tus' : list typ)
             (e : expr)
             (R : hlist typD (getUVars c) -> hlist typD (getUVars c) ->
                  hlist typD (getVars c ++ tvs) -> hlist typD tus -> hlist typD tus' -> Prop)
             (es : list (option expr)),
        mapD_nil tus tus' es R ->
        forall sD,
          ctx_substD (getUVars c) (getVars c) cs = Some sD ->
        forall gD : exprT (getUVars c ++ tus) _ Prop,
          propD (getUVars c ++ tus) (getVars c ++ tvs) e = Some gD ->
          exists gD' : exprT (getUVars c ++ tus') _ Prop,
            propD (getUVars c ++ tus') (getVars c ++ tvs)
                  (instantiate (do_instantiate cs base es) 0 e) =
            Some gD' /\
            (forall (_us : hlist typD (getUVars c)) _vsx (_vs : hlist typD _)
                    (us : hlist typD tus) (us' : hlist typD tus'),
                R _us _us (hlist_app _vsx _vs) us us' ->
                sD _us _vsx ->
                (gD' (hlist_app _us us') (hlist_app _vsx _vs) <->
                 gD (hlist_app _us us) (hlist_app _vsx _vs))).
    Proof.
      unfold propD, exprD_typ0.
      intros; forward; inv_all.
      eapply instantiate_do_instantiate_exprD_sound in H1; eauto.
      forward_reason.
      rewrite H1. eexists; split; eauto.
      intros. eapply H3 in H4; eauto.
      subst.
      autorewrite_with_eq_rw.
      rewrite H4.
      reflexivity.
    Qed.

    Lemma mapD_conv
    : forall a b c vs vs' us us' _us _us' es es' R
             (pf_vs:vs=vs') (pf_us:us=us') (pf_us':_us=_us'),
        es = es' ->
        (@mapD a b c vs  us _us es R <->
         @mapD a b c vs' us' _us' es'
               match pf_vs in _ = vs
                   , pf_us in _ = us
                   , pf_us' in _ = us'
                     return hlist _ a -> hlist _ b -> hlist _ vs ->
                            hlist _ us -> hlist _ us' -> hlist _ _ -> Prop
               with
                 | eq_refl , eq_refl , eq_refl => R
               end).
    Proof using.
      destruct pf_us. destruct pf_vs. destruct pf_us'. intros; subst.
      reflexivity.
    Qed.

    Lemma mapD_nil_conv
    : forall a a' b b' vs vs' us us' _us _us' es es' R
             (pf__us : a = a') (pf__us' : b = b') (pf_vs:vs=vs') (pf_us:us=us') (pf_us':_us=_us'),
        es = es' ->
        (@mapD_nil a b vs  us _us es R <->
         @mapD_nil a' b' vs' us' _us' es'
               match pf__us in _ = a
                   , pf__us' in _ = b
                   , pf_vs in _ = vs
                   , pf_us in _ = us
                   , pf_us' in _ = us'
                     return hlist _ a -> hlist _ b -> hlist _ vs ->
                            hlist _ us -> hlist _ us' -> Prop
               with
                 | eq_refl , eq_refl , eq_refl , eq_refl , eq_refl => R
               end).
    Proof using.
      intros; subst. reflexivity.
    Qed.

    Lemma mapD_app_lem
    : forall tus_base tus_base' tvs tus tus',
      forall es _post R,
        @mapD tus_base tus_base' _post tvs tus tus' es R ->
        forall ts ts' mlist_inst _tus_post R',
          @mapD (tus_base ++ tus) (tus_base' ++ tus') _tus_post tvs ts ts' mlist_inst R' ->
          forall (pf : ts' ++ _tus_post = _post),
          exists R'',
            @mapD tus_base tus_base' _tus_post tvs (tus ++ ts) (tus' ++ ts') (es ++ mlist_inst) R'' /\
            forall _us _us' vs us us' us'',
              R'' _us _us' vs us us' us'' <->
              (R _us _us' vs (fst (hlist_split _ _ us)) (fst (hlist_split _ _ us'))
                 match pf in _ = t return hlist _ t with
                 | eq_refl => hlist_app (snd (hlist_split _ _ us')) us''
                 end /\
               R' (hlist_app _us (fst (hlist_split _ _ us)))
                  (hlist_app _us' (fst (hlist_split _ _ us')))
                  vs (snd (hlist_split _ _ us)) (snd (hlist_split _ _ us')) us'').
    Proof. clear.
      induction 1.
      { simpl; intros ? ? ?.
        intros. setoid_rewrite hlist_app_nil_r.
        revert H; revert R'.
        generalize dependent (eq_sym (app_nil_r_trans _tus)).
        generalize dependent (eq_sym (app_nil_r_trans _tus')).
        generalize (_tus ++ nil); generalize (_tus' ++ nil); intros; subst.
        eexists; split; eauto.
        intros. intuition. }
      { Opaque hlist_split.
        simpl; intros; subst.
        cut (@mapD ((_tus ++ t :: nil) ++ tus) ((_tus' ++ t :: nil) ++ tus') _tus_post _tvs ts ts' mlist_inst
                   match eq_sym (app_ass_trans _ (t::nil) _) in _ = t
                       , eq_sym (app_ass_trans _ (t::nil) _) in _ = t'
                         return hlist (typD (RType:=RType_typ)) t -> hlist (typD (RType:=RType_typ)) t' -> _
                   with
                     | eq_refl , eq_refl => R'
                   end).
        { clear H0. intros.
          eapply IHmapD in H0; clear IHmapD.
          forward_reason.
          eexists; split.
          { simpl. constructor. eassumption. }
          simpl. intros.
          rewrite H1; clear H1. clear.
          Transparent hlist_split. simpl.
          change (fix app (l m : list typ) {struct l} :
                    list typ :=
                      match l with
                      | nil => m
                      | a0 :: l1 => a0 :: app l1 m
                      end) with (@app typ).
          destruct (@hlist_split typ (@typD typ RType_typ) tus ts
                                 (@hlist_tl typ (@typD typ RType_typ) t
                                            (tus ++ ts) us)).
          destruct (@hlist_split typ (@typD typ RType_typ) tus' ts'
                                 (@hlist_tl typ (@typD typ RType_typ) t
                                            (tus' ++ ts') us')).
          simpl. autorewrite_with_eq_rw.
          do 2 rewrite hlist_app_assoc.
          autorewrite_with_eq_rw.
          simpl. instantiate (1 := eq_refl).
          repeat rewrite <- and_assoc.
          eapply and_iff. reflexivity.
          intro. rewrite H0.
          tauto. }
        { revert H0. clear.
          destruct (@eq_sym (list typ) ((_tus ++ t :: @nil typ) ++ tus)
                            (_tus ++ (t :: @nil typ) ++ tus)
                            (@app_ass_trans typ _tus (t :: @nil typ) tus)).
          destruct (@eq_sym (list typ) ((_tus' ++ t :: @nil typ) ++ tus')
                            (_tus' ++ (t :: @nil typ) ++ tus')
                            (@app_ass_trans typ _tus' (t :: @nil typ) tus')).
          exact (fun x => x). } }
      { intros. subst.
        cut (@mapD ((_tus ++ t :: nil) ++ tus) (_tus' ++ tus') _tus_post _tvs ts ts' mlist_inst
                   match eq_sym (app_ass_trans _ (t::nil) _) in _ = t
                         return hlist _ t -> hlist _ _ -> _
                   with
                     | eq_refl => R'
                   end).
        { clear H; intros.
          eapply IHmapD in H; clear IHmapD.
          forward_reason. subst.
          rewrite exprD_conv
             with (pfu:=f_equal _ (app_ass_trans _ _ _)) (pfv:=eq_refl)
               in H0.
          autorewrite_with_eq_rw_in H0. forwardy.
          inv_all; subst.
          eexists; split.
          { simpl. constructor. eauto. eauto. }
          Opaque hlist_split.
          simpl. intros.
          rewrite H2; clear H2.
          autorewrite_with_eq_rw.
          rewrite <- and_assoc.
          eapply and_iff.
          { rewrite (hlist_eta us); simpl.
            rewrite hlist_hd_fst_hlist_split. simpl.
            rewrite (hlist_app_assoc' (fst _) (snd _) _).
            rewrite hlist_app_hlist_split.
            clear.
            destruct (app_ass_trans tus' ts' _tus_post). reflexivity. }
          intros. eapply and_iff.
          { rewrite hlist_hd_fst_hlist_split.
            rewrite hlist_tl_fst_hlist_split.
            instantiate (1:=eq_refl).
            reflexivity. }
          intros.
          rewrite hlist_app_assoc. autorewrite_with_eq_rw.
          rewrite hlist_tl_snd_hlist_split.
          eapply iff_eq. f_equal.
          rewrite (hlist_eta us). simpl.
          Transparent hlist_split. simpl.
          match goal with
          | |- context [ match ?X with _ => _ end ] =>
            destruct X
          end. reflexivity. }
        { revert H1. clear.
          revert R'.
          destruct (eq_sym (app_ass_trans _tus (t :: nil) tus)). tauto. } }
    Qed.

    Lemma list_substD_conv
    : forall tus tus' tvs tvs' n n' (s : list (option expr))
             (pfu : tus=tus') (pfv:tvs=tvs') (pfn : n=n'),
        FMapSubst.SUBST.list_substD tus tvs n s =
        match eq_sym pfu in _ = t
                            , eq_sym pfv in _ = t' return option (exprT t t' Prop) with
        | eq_refl , eq_refl => FMapSubst.SUBST.list_substD tus' tvs' n' s
        end.
    Proof.
      destruct pfu; destruct pfv; destruct 1; eauto.
    Qed.

    Lemma length_list_subst
    : forall a N b mlist,
        mlist = amap_aslist (expr:=expr) a b N ->
        length mlist = N.
    Proof.
      clear. induction N; simpl; intros; subst; auto.
      simpl. f_equal. eapply IHN. reflexivity.
    Qed.

    Lemma types_after_instantiate_map_fmap
    : forall f ts es,
        types_after_instantiate ts (map (Functor.fmap f) es) =
        types_after_instantiate ts es.
    Proof.
      induction ts; destruct es; simpl; auto.
      { destruct o; eauto.
        f_equal. eauto. }
    Qed.

    Lemma mapD_nil_ex
    : forall _tus _tus' tvs ts mlist R,
        @mapD_nil _tus _tus' tvs ts (types_after_instantiate ts mlist) mlist R ->
        forall _us _us' vs (us' : hlist _ (types_after_instantiate ts mlist)),
        exists us,
          R _us _us' vs us us'.
    Proof.
      clear. induction 1.
      { eauto. }
      { intros.
        destruct (IHmapD_nil (hlist_app _us (Hcons (hlist_hd us') Hnil))
                             (hlist_app _us' (Hcons (hlist_hd us') Hnil))
                             vs (hlist_tl us')).
        exists (Hcons (hlist_hd us') x).
        simpl. eauto. }
      { intros.
        destruct (IHmapD_nil (hlist_app _us (Hcons (eD (hlist_app _us' us') vs) Hnil))
                             _us' vs us').
        exists (Hcons (eD (hlist_app _us' us') vs) x).
        simpl. eauto. }
    Qed.

    Lemma mapD_nil_app
    : forall tus_base tus_base' tvs tus tus' es R,
        @mapD_nil tus_base tus_base' tvs tus tus' es R ->
        forall ts ts' mlist_inst R',
          @mapD_nil (tus_base ++ tus) (tus_base' ++ tus') tvs ts ts' mlist_inst R' ->
          exists R'',
            @mapD_nil tus_base tus_base' tvs (tus ++ ts) (tus' ++ ts') (es ++ mlist_inst) R'' /\
            forall __us __us' _us _us' vs us us',
              R'' __us __us' vs (hlist_app _us us) (hlist_app _us' us') <->
              (   R __us __us' vs _us _us'
                  /\ R' (hlist_app __us _us) (hlist_app __us' _us') vs us us').
    Proof.
      induction 1; simpl; intros.
      { intros.
        exists (match app_nil_r_trans _tus in _ = _tu
                    , app_nil_r_trans _tus' in _ = _tu'
                      return hlist _ _tu -> hlist _ _tu' -> _
                with
                | eq_refl , eq_refl => R'
                end).
        split.
        { destruct (app_nil_r_trans _tus).
          destruct (app_nil_r_trans _tus'). assumption. }
        { intros.
          rewrite (hlist_eta _us).
          rewrite (hlist_eta _us'). simpl.
          rewrite hlist_app_nil_r. rewrite hlist_app_nil_r.
          clear.
          generalize dependent (app_nil_r_trans _tus).
          generalize dependent (app_nil_r_trans _tus').
          generalize dependent (_tus' ++ nil).
          generalize dependent (_tus ++ nil).
          intros; subst. tauto. } }
      { apply (@mapD_nil_conv _ _ _ _ _tvs _ ts _ ts' _ mlist_inst _ R' (eq_sym (app_ass_trans _ (t::nil) _)) (eq_sym (app_ass_trans _ (t::nil) _)) eq_refl eq_refl eq_refl eq_refl) in H0.
        eapply IHmapD_nil in H0.
        forward_reason.
        eexists; split.
        { constructor; eauto. }
        { simpl. intros.
          specialize (H1 (hlist_app __us (Hcons (hlist_hd _us) Hnil))
                         (hlist_app __us' (Hcons (hlist_hd _us') Hnil))
                         (hlist_tl _us) (hlist_tl _us') vs us us').
          rewrite (hlist_eta _us). simpl.
          rewrite (hlist_eta _us'). simpl.
          rewrite <- and_assoc.
          apply and_iff. reflexivity. intros.
          destruct H2. rewrite H1.
          clear.
          rewrite hlist_app_assoc.
          rewrite hlist_app_assoc.
          generalize (app_ass_trans _tus (t :: nil) tus).
          generalize (app_ass_trans _tus' (t :: nil) tus').
          simpl.
          generalize ((_tus' ++ t :: nil) ++ tus').
          generalize ((_tus ++ t :: nil) ++ tus).
          intros; subst. simpl.
          tauto. } }
      { apply (@mapD_nil_conv _ _ _ _ _tvs _ ts _ ts' _ mlist_inst _ R' (eq_sym (app_ass_trans _ (t::nil) _)) eq_refl eq_refl eq_refl eq_refl eq_refl) in H1.
        eapply IHmapD_nil in H1; clear IHmapD_nil.
        forward_reason.
        eapply exprD_weakenU with (tus':=ts') in H0; [ | eauto ].
        forward_reason.
        rewrite exprD_conv
           with (pfu:=eq_sym (app_ass_trans _ _ _)) (pfv:=eq_refl)
             in H0.
        autorewrite_with_eq_rw_in H0.
        forwardy. inv_all; subst.
        eexists; split.
        { econstructor; eauto. }
        { simpl. intros.
          rewrite <- and_assoc.
          eapply and_iff.
          { rewrite (hlist_eta _us). simpl.
            rewrite hlist_app_assoc'.
            erewrite H3.
            instantiate (1 := us').
            clear. destruct (app_ass_trans _tus' tus' ts').
            tauto. }
          { intro.
            clear - H2.
            specialize (H2 (hlist_app __us (Hcons (hlist_hd _us) Hnil))
                           __us' (hlist_tl _us) _us' vs us us').
            rewrite (hlist_eta _us). simpl.
            rewrite H2. clear.
            apply and_iff. reflexivity. intro.
            rewrite hlist_app_assoc.
            autorewrite_with_eq_rw. tauto. } } }
    Qed.

    Lemma types_after_instantiate_Some_end
    : forall c t a b,
        length a = length b ->
        types_after_instantiate a b =
        types_after_instantiate (a ++ t :: nil) (b ++ Some c :: nil).
    Proof.
      induction a; destruct b; simpl; intros; auto.
      { inversion H. }
      { inversion H. }
      { rewrite IHa. reflexivity. omega. }
    Qed.


    Lemma types_after_instantiate_firstn_skipn
      : forall n ts es,
        types_after_instantiate (firstn n ts) (firstn n es) ++
                                types_after_instantiate (skipn n ts) (skipn n es) =
        types_after_instantiate ts es.
    Proof.
      induction n; simpl; intros; auto.
      { destruct ts; simpl.
        + destruct es; try reflexivity.
          destruct (skipn n es); reflexivity.
        + destruct es; [ | destruct o; simpl; try rewrite IHn ; reflexivity ].
          destruct (skipn n ts); reflexivity. }
    Qed.

    Ltac inst_hlists :=
      repeat match goal with
             | h : hlist _ _ , H : forall x : hlist _ _, _ |- _ =>
               first [ specialize (H h)
                     | specialize (H (fst (hlist_split _ _ h))) ]
             | h : hlist _ _ , h' : hlist _ _ , H : forall x : hlist _ _, _  |- _ =>
               specialize (H (hlist_app h h'))
             | h : hlist _ _ , h' : hlist _ _ , h'' : hlist _ _ , H : forall x : hlist _ _, _ |- _ =>
               first [ specialize (H (hlist_app h (hlist_app h' h'')))
                     | specialize (H (hlist_app (hlist_app h h') h'')) ]
             end.


    Fixpoint Forgetting ts (es : list (option expr))
      : hlist typD ts -> hlist typD (types_after_instantiate ts es) -> Prop :=
      match ts as ts , es as es
            return hlist typD ts -> hlist typD (types_after_instantiate ts es) -> Prop
      with
      | nil , nil => @eq _
      | nil , _ :: _ => @eq _
      | t :: ts , None :: es => fun a b => hlist_hd a = hlist_hd b
                                           /\ @Forgetting ts es (hlist_tl a) (hlist_tl b)
      | t :: ts , Some _ :: es => fun a b => @Forgetting ts es (hlist_tl a) b
      | _ :: _ , nil => fun _ _ => False
      end.

    Fixpoint Forget ts (es : list (option expr))
    : hlist typD ts -> hlist typD (types_after_instantiate ts es) :=
      match ts as ts , es as es
            return hlist typD ts -> hlist typD (types_after_instantiate ts es)
      with
      | nil , nil => fun x => x
      | nil , _ :: _ => fun x => x
      | t :: ts , nil => fun _ => Hnil
      | t :: ts , None :: es => fun x =>
                                  Hcons (hlist_hd x) (@Forget ts es (hlist_tl x))
      | t :: ts , Some _ :: es => fun x => @Forget ts es (hlist_tl x)
      end.

    Lemma mapD_nil_Forgetting'
    : forall a b c d e f R,
        @mapD_nil a b c d e f R ->
        forall A B C D E,
          R A B C D E ->
          exists pf : e = types_after_instantiate d f,
            Forgetting f D match pf in _ = t return hlist _ t with
                           | eq_refl => E
                           end.
    Proof.
      clear. induction 1; simpl; intros; subst.
      { exists eq_refl. reflexivity. }
      { forward_reason.
        eapply IHmapD_nil in H1.
        forward_reason. exists (f_equal _ x).
        subst. eauto. }
      { forward_reason.
        eapply IHmapD_nil in H2.
        forward_reason. subst.
        exists eq_refl. auto. }
    Qed.

    Lemma mapD_nil_Forgetting
    : forall a b c d f R,
        @mapD_nil a b c d _ f R ->
        forall A B C D E,
          R A B C D E ->
          Forgetting f D E.
    Proof.
      intros.
      generalize (@mapD_nil_Forgetting' a b c0 d _ f R H _ _ _ _ _ H0).
      intros; forward_reason.
      cutrewrite (x = eq_refl) in H1; auto.
      unfold tenv in *.
      apply UIP_refl.
    Qed.

    Lemma the_actual_lemma
    : forall f (_tus _tus' tvs : tenv typ) (a : amap expr)
        (WFa : FMapSubst.SUBST.WellFormed a),
        forall (tus_ tus tus' : tenv typ) mlist1_inst
          (Hlen : length mlist1_inst = length tus),
          let mlist2 := amap_aslist a (length (_tus ++ tus)) (length tus_) in
          let mlist2_inst := map (Functor.fmap f) mlist2 in
          forall R sD' P
            (HmapD : @mapD _tus
                  _tus'
                  (types_after_instantiate tus_ mlist2)
                  tvs
                  tus
                  tus'
                  mlist1_inst R)
            (HsubstD : FMapSubst.SUBST.list_substD
              (_tus ++ tus ++ tus_)
              tvs
              (length (_tus ++ tus))
              mlist2 = Some sD')
            (Hf : forall (n : nat) e t eD,
                nth_error mlist2 n = Some (Some e) ->
                exprD (_tus ++ tus ++ tus_) tvs t e = Some eD ->
                exists eD',
                  exprD (_tus' ++ tus' ++ types_after_instantiate tus_ mlist2)
                         tvs t (f e) = Some eD' /\
                  forall _us _us' vs us us' us_ us_',
                    forall HP : P _us _us' vs,
                    forall Hfor : Forgetting mlist2 us_ us_',
                    R _us _us' vs us us' us_' ->
                    eD (hlist_app _us (hlist_app us us_)) vs =
                    eD' (hlist_app _us' (hlist_app us' us_')) vs),
            exists R',
              @mapD_nil _tus _tus' tvs (tus ++ tus_)
                        (tus' ++
                         types_after_instantiate tus_ mlist2)
                        (mlist1_inst ++ mlist2_inst)  R' /\
              forall _us _us' vs us us' us_',
                forall (HP : P _us _us' vs),
                R _us _us' vs us us' us_' ->
                exists us_,
                  Forgetting mlist2 us_ us_' /\
                  sD' (hlist_app _us (hlist_app us us_)) vs /\
                  R' _us _us' vs (hlist_app us us_) (hlist_app us' us_').
    Proof.
      clear. induction tus_; intros.
      { simpl. simpl in *.
        eapply mapD_mapD_nil in HmapD.
        forward_reason.
        eapply mapD_nil_conv
          with (pf_us:=eq_sym (app_nil_r_trans _))
               (pf_us':=eq_sym (app_nil_r_trans _))
               (pf_vs:=eq_refl)
               (pf__us:=eq_refl) (pf__us':=eq_refl) in H.
        eexists; split.
        { eapply H. }
        { clear H.
          intros.
          inv_all. subst. exists Hnil.
          rewrite (hlist_eta us_').
          split; auto. split; auto.
          autorewrite_with_eq_rw.
          do 2 rewrite hlist_app_nil_r.
          autorewrite_with_eq_rw.
          eapply H0. eauto. }
        { unfold mlist2_inst. symmetry. apply app_nil_r_trans. } }
      { simpl in *. subst mlist2. subst mlist2_inst.
        consider (amap_lookup (length (_tus ++ tus)) a);
          intros; forwardy; inv_all; subst.
        { eapply nth_error_get_hlist_nth_appR in H0;
          [ simpl in H0; forward_reason | repeat rewrite app_length; simpl; omega ].
          eapply nth_error_get_hlist_nth_appR in H0;
          [ simpl in H0; forward_reason | repeat rewrite app_length; simpl; omega ].
          rewrite app_length in H0.
          replace (length _tus + length tus - length _tus - length tus) with 0 in H0 by omega.
          inv_all. subst.
          specialize (IHtus_ (tus ++ a0 :: nil) tus' (mlist1_inst ++ Some (f e) :: nil)).
          eapply Hf in H1. 2: instantiate (1 :=0); reflexivity.
          destruct H1 as [ eD' [ HeD' HeD'eq ] ].
          rewrite exprD_conv
            with (pfu:=app_ass_trans _ _ _) (pfv:=eq_refl) in HeD'.
          autorewrite_with_eq_rw_in HeD'. forwardy.
          edestruct (@mapD_app_lem _ _ _ _ _ _ _ _ HmapD (a0 :: nil) nil (Some (f e) :: nil)).
          { constructor. constructor. simpl. eassumption. }
          revert H6; instantiate (1 := eq_refl); intro H6.
          destruct H6 as [ HmapD' ? ].
          assert (Heq : S (@length typ (_tus ++ tus)) = length (_tus ++ tus ++ a0 :: nil)).
          { repeat rewrite app_length. simpl. omega. }
          destruct Heq.
          eapply mapD_conv
              with (pf_vs:=eq_refl)
                   (pf_us:=eq_refl) (pf_us':=app_nil_r_trans _)
              in HmapD'; [ | reflexivity ].
          erewrite list_substD_conv
               with (pfu:=eq_sym (f_equal (app _) (app_ass_trans tus (a0::nil) tus_)))
                    (pfv:=eq_refl)
              in H2; [ | reflexivity ].
          simpl in H2.
          autorewrite_with_eq_rw_in H2. forwardy.
          edestruct IHtus_ with (P:=P).
          { repeat rewrite app_length. simpl. omega. }
          { eapply HmapD'. }
          { eapply H2. }
          { inv_all. subst. clear - Hf H H3 H4 H6.
            do 4 intro. intro Hnth. intro H0.
            rewrite exprD_conv
              with (pfu:=f_equal _ (eq_sym (app_ass_trans _ _ _))) (pfv:=eq_refl) in H0.
            simpl in H0. autorewrite_with_eq_rw_in H0.
            forwardy.
            eapply Hf in H0; clear Hf. 2: instantiate (1 := S n); eassumption.
            inv_all. subst.
            destruct H0 as [ ? [ ? ? ] ].
            eexists; split; eauto.
            intros.
            inst_hlists.
            autorewrite_with_eq_rw_in H2.
            eapply H6 in H2; clear H6.
            specialize (H1 (hlist_app (snd (hlist_split _ _ us)) us_) us_').
            rewrite <- H1; try eassumption.
            { autorewrite_with_eq_rw.
              generalize (hlist_app_assoc' (fst (hlist_split _ _ us)) (snd (hlist_split tus (a0 :: nil) us)) us_).
              intro XXX; change_rewrite XXX; clear XXX.
              rewrite hlist_app_hlist_split.
              generalize (hlist_app us us_).
              clear. intros.
              generalize (app_ass_trans tus (a0 :: nil) tus_).
              simpl. generalize dependent (tus ++ (a0 :: tus_)).
              intros; subst. reflexivity. }
            { revert Hfor.
              clear.
              generalize (snd (hlist_split tus (a0 :: nil) us)).
              intro h. rewrite (hlist_eta h).
              rewrite (hlist_eta (hlist_tl h)).
              simpl. tauto. }
            { destruct H2 as [ ? [ ? ? ] ].
              { revert H2. clear.
                simpl.
                rewrite (hlist_eta (snd _)).
                apply impl_eq. f_equal.
                rewrite <- hlist_app_nil_r.
                rewrite hlist_split_hlist_app. reflexivity. } } }
          { destruct H8 as [ H8 ? ].
            eapply mapD_nil_conv
              with (pf__us:=eq_refl) (pf__us':=eq_refl) (pf_vs:=eq_refl)
                   (pf_us:=app_ass_trans _ _ _)
                   (pf_us':=eq_refl)
              in H8.
            { eexists; split; eauto.
              intros.
              inv_all. subst.
              inst_hlists. clear IHtus_ H8.
              pose (y1 (hlist_app (hlist_app _us' us') us_') vs : typD a0).
              simpl in *.
              destruct (H9 (hlist_app us (Hcons t0 Hnil)) us' us_');
                clear H9; try eassumption.
              { autorewrite_with_eq_rw. eapply H6; clear H6.
                repeat rewrite hlist_split_hlist_app. simpl.
                rewrite <- hlist_app_nil_r.
                rewrite hlist_split_hlist_app. simpl.
                auto. }
              { destruct H1.
                specialize (HeD'eq (Hcons t0 x1) _ HP H1 H10).
                exists (Hcons t0 x1).
                rewrite H3; clear H3.
                rewrite H4; clear H4.
                simpl.
                revert HeD'eq. revert H5.
                autorewrite_with_eq_rw.
                rewrite hlist_app_assoc. simpl.
                generalize (app_ass_trans tus (a0 :: nil) tus_).
                generalize (hlist_app us (Hcons t0 x1)).
                simpl.
                generalize dependent ((tus ++ a0 :: nil) ++ tus_).
                intros; subst; simpl in *. subst t0.
                intuition.
                rewrite HeD'eq. clear.
                f_equal.
                rewrite hlist_app_assoc. reflexivity. } }
            { rewrite app_ass. reflexivity. } } }
        { (** this is the None case **)
          specialize (IHtus_ (tus ++ a0 :: nil) (tus' ++ a0::nil) (mlist1_inst ++ None :: nil)).
          assert (length (_tus ++ tus ++ a0::nil) = S (length (_tus ++ tus))).
          { repeat rewrite app_length. simpl. omega. }
          destruct H0.
          edestruct (fun R pf => @mapD_app_lem _ _ _ _ _ _ _ _ HmapD (a0::nil) (a0::nil) (None::nil)
                                    (types_after_instantiate tus_
                                                             (amap_aslist a (length (_tus ++ tus ++ a0::nil)) (length tus_))) R pf eq_refl).
          { constructor. constructor. }
          destruct H0.
          edestruct IHtus_ with (P:=P).
          { do 2 rewrite app_length. simpl. f_equal. assumption. }
          { eapply H0. }
          { revert HsubstD.
            instantiate (1 := match eq_sym (f_equal (app _tus) (app_ass_trans _ (a0::nil) _)) in _ = t return exprT t _ _ with
                              | eq_refl => sD'
                              end).
            clear.
            generalize (app_ass_trans tus (a0 :: nil) tus_).
            generalize ((tus ++ a0 :: nil) ++ tus_). intros; subst.
            assumption. }
          { rename H1 into HxR.
            clear - Hf HxR. intros.
            destruct (Hf (S n) _ t
                         match f_equal _ (app_ass_trans _ _ _) in _ = t return exprT t _ _ with
                         | eq_refl => eD
                         end H); clear Hf; eauto.
            { generalize dependent (app_ass_trans tus (a0 :: nil) tus_).
              generalize dependent ((tus ++ a0 :: nil) ++ tus_).
              intros; subst. eassumption. }
            { clear - H1 HxR.
              exists (match eq_sym (f_equal (app _tus') (app_ass_trans tus' (a0::nil) _)) in _ = t
                            return exprT t _ _
                      with
                      | eq_refl => x0
                      end).
              destruct H1.
              split.
              { clear - H. revert H.
                uip_all'. destruct e0. assumption. }
              { intros. eapply HxR in H1. revert H1. revert HP.
                clear - H0 Hfor.
                intros.
                specialize (H0 _us _us' vs (fst (hlist_split _ _ us))
                               (fst (hlist_split _ _ us'))
                               (hlist_app (snd (hlist_split _ _ us)) us_)
                               (hlist_app (snd (hlist_split _ _ us')) us_')).
                revert H0.
                autorewrite_with_eq_rw.
                intros.
                forward_reason.
                revert H0.
                clear - HP Hfor H2 H1 H.
                generalize (hlist_app_assoc' (fst (hlist_split tus (a0::nil) us)) (snd (hlist_split tus (a0::nil) us)) us_).
                intro XXX. change_rewrite XXX; clear XXX.
                generalize (hlist_app_assoc' (fst (hlist_split tus' (a0::nil) us')) (snd (hlist_split tus' (a0::nil) us')) us_').
                intro XXX. change_rewrite XXX; clear XXX.
                repeat rewrite hlist_app_hlist_split.
                generalize (app_ass_trans tus' (a0 :: nil)
                                          (types_after_instantiate tus_
                                                                   (amap_aslist a (length (_tus ++ tus ++ a0 :: nil))
                                                                                (length tus_)))).
                simpl.
                match goal with
                | |- forall x : _ = ?X, _ => generalize dependent X; intros; subst
                end.
                simpl in *.
                etransitivity; [ | eapply H0; eauto ].
                { f_equal.
                  clear.
                  generalize (hlist_app us us_).
                  generalize (app_ass_trans tus (a0 :: nil) tus_).
                  match goal with
                  | |- forall x : ?X = _, _ => generalize dependent X; intros; subst
                  end.
                  reflexivity. }
                { clear H0.
                  generalize dependent (snd (hlist_split tus (a0 :: nil) us)).
                  generalize dependent (snd (hlist_split _ (a0 :: nil) us')).
                  clear - Hfor.
                  intros.
                  rewrite (hlist_eta h0). rewrite (hlist_eta h).
                  rewrite (hlist_eta (hlist_tl h0)).
                  rewrite (hlist_eta (hlist_tl h)).
                  simpl. split; auto. } } } }
          { rename H1 into HxR. clear - H2 HxR.
            exists (match app_ass_trans tus (a0 ::nil) tus_ in _ = t
                        , app_ass_trans tus' (a0::nil) _ in _ = t'
                          return _ -> _ -> _ -> hlist _ t -> hlist _ t' -> _ with
                    | eq_refl , eq_refl => x0
                    end).
            destruct H2; split.
            { clear - H. uip_all'.
              repeat match goal with
                     | H : _ = ?X |- _ => generalize dependent X; intros; subst
                     | H : ?X = _ |- _ => generalize dependent X; intros; subst
                     end.
              revert H.
              rewrite app_ass. auto. }
            { clear - H0 HxR.
              intros.
              generalize (H0 _us _us' vs
                             (hlist_app us (fst (hlist_split (a0::nil) _ us_')))
                             (hlist_app us' (fst (hlist_split (a0::nil) _ us_')))
                             (snd (hlist_split (a0::nil) _ us_'))); clear H0.
              repeat rewrite hlist_split_hlist_app; simpl.
              rewrite (hlist_eta us_') in H.
              destruct 1; eauto.
              { eapply HxR.
                repeat rewrite hlist_split_hlist_app; simpl. tauto. }
              exists (Hcons (hlist_hd us_') x1).
              revert H0.
              repeat rewrite hlist_app_assoc. simpl.
              generalize dependent (app_ass_trans tus (a0 :: nil) tus_).
              generalize dependent (app_ass_trans tus' (a0 :: nil)
                                                  (types_after_instantiate tus_
                                                     (amap_aslist a (length (_tus ++ tus ++ a0 :: nil))
                                                                  (length tus_)))).
              intros.
              repeat match goal with
                     | H : ?X = _ |- _ => generalize dependent X; intros; subst
                     end.
              simpl in *.
              split; try tauto. rewrite (hlist_eta us_'). simpl. tauto. } } } }
    Qed.

    Lemma the_actual_lemma'
    : forall f (_tus _tus' tvs : tenv typ) (a : amap expr)
        (WFa : FMapSubst.SUBST.WellFormed a),
        forall (tus_ tus tus' : tenv typ) mlist1_inst mlist2 mlist2_inst
          (Hlen : length mlist1_inst = length tus),
          mlist2 = amap_aslist a (length (_tus ++ tus)) (length tus_) ->
          mlist2_inst = map (Functor.fmap f) mlist2 ->
          forall R sD' P
            (HmapD : @mapD _tus
                  _tus'
                  (types_after_instantiate tus_ mlist2)
                  tvs
                  tus
                  tus'
                  mlist1_inst R)
            (HsubstD : FMapSubst.SUBST.list_substD
              (_tus ++ tus ++ tus_)
              tvs
              (length (_tus ++ tus))
              mlist2 = Some sD')
            (Hf : forall (n : nat) e t eD,
                nth_error mlist2 n = Some (Some e) ->
                exprD (_tus ++ tus ++ tus_) tvs t e = Some eD ->
                exists eD',
                  exprD (_tus' ++ tus' ++
                          types_after_instantiate tus_ mlist2)
                         tvs t (f e) = Some eD' /\
                  forall _us _us' vs us us' us_ us_',
                    P _us _us' vs ->
                    Forgetting _ us_ us_' ->
                    R _us _us' vs us us' us_' ->
                    eD (hlist_app _us (hlist_app us us_)) vs =
                    eD' (hlist_app _us' (hlist_app us' us_')) vs),
            exists R',
              @mapD_nil _tus _tus' tvs (tus ++ tus_)
                        (tus' ++
                         types_after_instantiate tus_ mlist2)
                        (mlist1_inst ++ mlist2_inst)  R' /\
              forall _us _us' vs us us' us_',
                P _us _us' vs ->
                R _us _us' vs us us' us_' ->
                exists us_,
                  sD' (hlist_app _us (hlist_app us us_)) vs /\
                  R' _us _us' vs (hlist_app us us_) (hlist_app us' us_').
    Proof.
      clear. intros. subst.
      eapply the_actual_lemma in HsubstD; eauto.
      forward_reason.
      eexists; split; eauto.
      intros. edestruct H0; eauto.
      forward_reason; eexists; split; eauto.
    Qed.

    Lemma do_instantiate_app
      : forall c (cs : ctx_subst c) base es es' u,
        do_instantiate cs base (es ++ es') u =
        if u ?[ lt ] (base + length es) then
          do_instantiate cs base es u
        else
          Some (lookup_compress es' (base + length (filter (fun x => match x with
                                                                     | Some _ => false
                                                                     | None => true
                                                                     end) es))
                                (u - base - length es)).
    Proof.
      clear. intros.
      unfold do_instantiate.
      generalize (lt_rem_sound base u).
      destruct (lt_rem u base); intros.
      { destruct H. subst.
        consider (u ?[ lt ] (base + length es)).
        { intros. rewrite lookup_compress_app.
          consider ((u - base) ?[ lt ] length es); auto.
          intros. exfalso. omega. }
        { intros. rewrite lookup_compress_app.
          consider ((u - base) ?[ lt ] length es); auto.
          { intros. exfalso. omega. } } }
      { consider (u ?[ lt ] (base + length es)); auto.
        intros.
        exfalso; omega. }
    Qed.

    Lemma mapD_nil_weaken_tvs
    : forall _tus _tus' _tvs _tvs' tus tus' es P,
        @mapD_nil _tus _tus' _tvs tus tus' es P ->
        exists P',
          @mapD_nil _tus _tus' (_tvs ++ _tvs') tus tus' es P' /\
          forall U U' V V' a b,
            P U U' V a b <-> P' U U' (hlist_app V V') a b.
    Proof.
      induction 1; simpl; intros.
      { eexists. split. constructor.
        simpl. intros; tauto. }
      { forward_reason.
        eexists; split.
        - econstructor. eauto.
        - simpl. intros. rewrite H1. reflexivity. }
      { eapply exprD_weakenV with (tvs':=_tvs') in H0; eauto.
        forward_reason.
        eexists; split.
        - econstructor; eauto.
        - simpl. intros.
          rewrite <- H2. rewrite <- H3. reflexivity. }
    Qed.

    Lemma minify_goal_sound_lem
    : forall g tus tvs tus' es g',
        minify_goal es (length (getUVars c ++ tus)) g = g' ->
        WellFormed_Goal (getUVars c ++ tus) (getVars c ++ tvs) g ->
        WellFormed_Goal (getUVars c ++ tus') (getVars c ++ tvs) g' /\
        forall gD (sD : exprT (getUVars c) (getVars c) Prop) R,
          goalD (getUVars c ++ tus) (getVars c ++ tvs) g = Some gD ->
          forall (Hsubst : substD (getUVars c) (getVars c) cs = Some sD)
                 (Hes_tus_len : length es = length tus),
          @mapD_nil (getUVars c) (getUVars c) (getVars c ++ tvs) tus tus' es R ->
          exists gD',
            goalD (getUVars c ++ tus') (getVars c ++ tvs) g' = Some gD' /\
            forall _us _vs vs us us',
              R _us _us (hlist_app _vs vs) us us' ->
              sD _us _vs ->
              (gD' (hlist_app _us us') (hlist_app _vs vs) ->
               gD (hlist_app _us us) (hlist_app _vs vs)).
    Proof.
      induction g.
      { (* All *)
        clear base_is_nus.
        simpl. intros. inv_all.
        specialize (IHg tus (tvs ++ t :: nil) tus' es _ eq_refl).
        destruct IHg.
        { rewrite app_ass in H0. assumption. }
        split.
        { subst. eapply WellFormed_Goal_GAll_do_solved. constructor.
          rewrite app_ass. assumption. }
        intros; forward; inv_all; subst.
        simpl.
        generalize (@GAll_do_solved_respects typ expr _ _ _ (getUVars c ++ tus')
                                             (getVars c ++ tvs) t
                    _ _ (Reflexive_EqGoal _ _ (minify_goal es (length (getUVars c ++ tus)) g))).
        destruct 1. clear H.
        rewrite goalD_conv
           with (pfu:=eq_refl) (pfv:=eq_sym (app_ass_trans _ _ _)) in H3.
        autorewrite_with_eq_rw_in H3. forwardy. inv_all; subst.
        destruct (mapD_nil_weaken_tvs (t::nil) H4) as [ ? [ ? ? ] ].
        eapply mapD_nil_conv
          with (pf_us':=eq_refl) (pf_us:=eq_refl) (pf_vs:=app_ass_trans _ _ _)
               (pf__us:=eq_refl) (pf__us':=eq_refl)
          in H3; [ | reflexivity ].
        specialize (H2 _ _ _ H Hsubst Hes_tus_len H3).
        forward_reason.
        rewrite goalD_conv
           with (pfu:=eq_refl) (pfv:=app_ass_trans _ _ _) in H2.
        autorewrite_with_eq_rw_in H2. forwardy.
        simpl in H5. change_rewrite H2 in H5.
        inversion H5; clear H5; subst.
        eexists; split; eauto.
        inv_all; subst.
        intros.
        autorewrite_with_eq_rw.
        generalize (H7 _us _vs (hlist_app vs (Hcons x0 Hnil)) us us'); clear H7. intros.
        rewrite <- hlist_app_assoc'.
        eapply H7; eauto.
        { autorewrite_with_eq_rw.
          rewrite <- hlist_app_assoc.
          eapply H6. eassumption. }
        { autorewrite_with_eq_rw.
          rewrite <- hlist_app_assoc.
          eapply H11 in H10; first [ eassumption | reflexivity ]. } }

      { (* Exs *)
        cbv beta iota delta [ minify_goal ]; fold minify_goal.
        intros.
        simpl in H.
        remember (amap_aslist a (length (getUVars c ++ tus)) (length l)) as mlist.
        match goal with
          | _ : GExs_nil_check ?X _ _ = _ |- _ =>
            remember X as ts'
        end.
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
        destruct (@GExs_nil_check_respects _ _ _ _ _
                    (getUVars c ++ tus') (getVars c ++ tvs) ts' (amap_empty expr)
                    (only_in_range_empty _ _)
                    (@WellFormed_amap_amap_empty _ _ _ _) _ _
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
        rewrite H in *; clear  H.
        simpl in *; intros. forwardy; inv_all. subst gD.
        rewrite goalD_conv
           with (pfu:=eq_sym (app_ass_trans _ _ _)) (pfv:=eq_refl)
             in H.
        autorewrite_with_eq_rw_in H. forwardy.
        inv_all. subst y.
        eapply amap_substD_list_substD in H6; eauto.

        assert (Hmlist_ts_length : length ts = length mlist).
        { clear - Heqmlist. symmetry. eapply length_list_subst. eauto. }
        assert (Hes_tus_len' : length (es ++ mlist_inst) = length (tus ++ ts)).
        { do 2 rewrite app_length. rewrite Hmlist_ts_length.
          rewrite Hes_tus_len. f_equal.
          subst mlist_inst. rewrite map_length. reflexivity. }
        specialize (fun R => H3 _ _ R H Hsubst Hes_tus_len').
        generalize H4; intro H_remember_mapD_nil.

        change (fun x2 : option expr =>
                  match x2 with
                  | Some x3 =>
                    Some
                      (instantiate
                         (do_instantiate cs base (es ++ mlist)) 0
                         x3)
                  | None => None
                  end)
          with (Functor.fmap (F:=option) (instantiate (do_instantiate cs base (es ++ mlist)) 0)) in *.
        forward_reason.
        eapply mapD_nil_mapD_iff in H4.
        destruct H4 as [ ? [ H4 Heq_mapD_mapD_nil ] ].
        eapply mapD_weaken_post
          with (_tus_post':=types_after_instantiate ts mlist)
            in H4.
        destruct H4 as [ ? [ H4 Heq_mapD_weaken ] ].
        rewrite <- Heqmlist in H6.
        erewrite list_substD_conv
           with (pfu:=app_ass_trans _ _ _) (pfv:=eq_refl) in H6 by reflexivity.
        simpl in H6; autorewrite_with_eq_rw_in H6. forwardy.
        destruct (fun H =>
                      @the_actual_lemma'
                        (instantiate (do_instantiate cs base (es ++ mlist)) 0)
                        (getUVars c) (getUVars c) (getVars c ++ tvs) a H
                        ts tus tus' es mlist mlist_inst Hes_tus_len Heqmlist Heqmlist_inst
                        _ _ (fun us us' vs => us = us' /\ sD us' (fst (hlist_split _ _ vs))) H4 H6).
        { destruct H2. tauto. }
        { (** Side condition **)
          revert H4. revert H6. revert Heqmlist Heqmlist_inst. revert H2.
          clear - Hes_tus_len Hmlist_ts_length base_is_nus RTypeOk_typ ExprOk_expr
                  ExprUVarOk_expr H_remember_mapD_nil Hsubst
                  Heq_mapD_weaken Heq_mapD_mapD_nil WF_cs.
          simpl; intros H2 Heqmlist Heqmlist_inst H6 H4 n e t eD H H0.
          unfold instantiate in *.
          edestruct (@expr_subst_sound _ _ _ _ _
                         (do_instantiate cs base (es ++ mlist)) (fun _ => None)
                         0 e _ eq_refl nil
                         (getUVars c ++ tus ++ ts) (getVars c ++ tvs)
                         (getUVars c ++ tus' ++ types_after_instantiate ts mlist) (getVars c ++ tvs)
          (fun us vs us' vs' =>
             vs = vs' /\
             sD (fst (hlist_split _ _ us')) (fst (hlist_split _ _ vs)) /\
             fst (hlist_split _ _ us) = fst (hlist_split _ _ us') /\
             x1 (fst (hlist_split _ _ us)) (fst (hlist_split _ _ us')) vs
                (fst (hlist_split _ _ (snd (hlist_split _ _ us))))
                (fst (hlist_split _ _ (snd (hlist_split _ _ us'))))
                (snd (hlist_split _ _ (snd (hlist_split _ _ us')))) /\
             Forgetting mlist
                        (snd (hlist_split _ _ (snd (hlist_split _ _ us))))
                        (snd (hlist_split _ _ (snd (hlist_split _ _ us'))))));
            try first [ reflexivity | eassumption ].
          { clear H0 eD.
            intros.
            assert (u < length (getUVars c ++ tus) \/
                    (u >= length (getUVars c ++ tus) /\
                     nth_error mlist (u - length (getUVars c ++ tus)) = Some None)).
            { assert (u < length (getUVars c ++ tus) \/ u >= length (getUVars c ++ tus)) by omega.
              destruct H3; auto.
              right. split; auto.
              apply nth_error_get_hlist_nth_Some in H1.
              simpl in H1. forward_reason.
              clear H1.
              apply ListNth.nth_error_length_lt in x.
              clear - H0 H3 H H6 Heqmlist H2 x.
              subst. rewrite amap_aslist_nth_error.
              rewrite rel_dec_eq_true; eauto with typeclass_instances.
              { rewrite amap_aslist_nth_error in H.
                consider (n ?[ lt ] length ts); try congruence. intros.
                inv_all. destruct H2.
                eapply H2 in H1. red in H1.
                eapply H1 in H0.
                cutrewrite (length (getUVars c ++ tus) + (u - length (getUVars c ++ tus)) = u); [ | omega ].
                f_equal.
                unfold amap_lookup.
                apply FMapSubst.SUBST.FACTS.not_find_in_iff. assumption. }
              { clear - x H3.
                repeat rewrite app_length in *. omega. } }
            clear H0.
            rewrite do_instantiate_app.
            destruct H3.
            { rewrite rel_dec_eq_true.
              2: eauto with typeclass_instances.
              2:{ rewrite Hes_tus_len. subst base. rewrite <- app_length. assumption. }
              rewrite nth_error_get_hlist_nth_conv with (pf:=app_ass_trans _ _ _) in H1.
              autorewrite_with_eq_rw_in H1.
              forwardy.
              eapply nth_error_get_hlist_nth_appL in H0.
              setoid_rewrite H1 in H0.
              forward_reason.
              eapply do_instantiate_sound with (es:=es) (tus':=tus') (tvs:=tvs) in H5; eauto.
              { destruct (do_instantiate cs base es u).
                { forward_reason.
                  eapply exprD_weakenU with (tus':=types_after_instantiate ts mlist) in H5;
                    eauto with typeclass_instances.
                  forward_reason.
                  rewrite exprD_conv
                     with (pfu:=eq_sym (app_ass_trans _ _ _)) (pfv:=eq_refl) in H5.
                  autorewrite_with_eq_rw_in H5. forwardy.
                  inv_all. subst. subst.
                  generalize (@Data.SigT.eq_sigT_rw _ _ (fun x1 y => hlist (typD (RType:=RType_typ)) x1 -> typD (RType:=RType_typ) y)).
                  simpl. intro XXX; rewrite XXX in H3; clear XXX.
                  autorewrite_with_eq_rw_in H3.
                  inv_all. subst.
                  eexists; split; try eassumption.
                  subst. intros us vs us' vs'.
                  simpl; intros; forward_reason.
                  subst.
                  simpl in *.
                  Ltac shatter hl :=
                    let rec it hl k :=
                        match type of hl with
                        | hlist ?T (?X ++ ?Y) =>
                          it (fst (hlist_split _ _ hl)) ltac:(fun x =>
                            it (snd (hlist_split _ _ hl)) ltac:(fun y =>
                              k (hlist_app x y)))
                        | _ => k hl
                        end
                    in
                    let rec f hl :=
                        match type of hl with
                        | hlist ?T (?X ++ ?Y) =>
                          f (fst (hlist_split _ _ hl)) ;
                          f (snd (hlist_split _ _ hl))
                        | _ => generalize dependent hl
                        end
                    in
                    it hl ltac:(fun x => assert (hl = x) by
                                          (repeat (rewrite hlist_app_hlist_split; simpl) ; reflexivity) ; f hl ; intros).
                  shatter us; shatter us'; shatter vs'.
                  specialize (H9 (hlist_app h4 h3) (hlist_app h6 h5) h2).
                  specialize (H8 (hlist_app h1 h0) h6 h5 (hlist_app h4 h3) h5).
                  specialize (H7 (hlist_app h1 h0) h).
                  revert H9.
                  autorewrite_with_eq_rw.
                  rewrite <- hlist_app_assoc'.
                  subst. rewrite <- hlist_app_assoc.
                  repeat rewrite hlist_split_hlist_app in H8. simpl in H8.
                  intros. etransitivity; eauto.
                  etransitivity; [ eapply H8; auto | eauto ].
                  split; auto. split; auto.
                  eapply Heq_mapD_mapD_nil; clear Heq_mapD_mapD_nil.
                  eapply Heq_mapD_weaken; eauto. }
                { forward_reason.
                  eapply nth_error_get_hlist_nth_weaken
                    with (ls':=types_after_instantiate ts mlist)
                      in H5.
                  simpl in H5; forward_reason.
                  rewrite nth_error_get_hlist_nth_conv
                     with (pf:=eq_sym (app_ass_trans _ _ _)) in H5.
                  autorewrite_with_eq_rw_in H5.
                  forwardy.
                  inv_all; subst.
                  destruct y1.
                  autorewrite_with_eq_rw_in H3.
                  generalize (@Data.SigT.eq_sigT_rw _ _ (fun x1 y => hlist (typD (RType:=RType_typ)) x1 -> typD (RType:=RType_typ) y)).
                  simpl. intro XXX; rewrite XXX in H3; clear XXX.
                  inv_all; subst. subst.
                  generalize (@Data.SigT.eq_sigT_rw _ _ (fun x1 y => hlist (typD (RType:=RType_typ)) x1 -> typD (RType:=RType_typ) y)).
                  simpl. intro XXX; rewrite XXX in H10; clear XXX.
                  simpl in H10.
                  autorewrite_with_eq_rw_in H10.
                  inv_all; subst; subst. simpl in *. subst.
                  eexists; split; eauto.
                  subst. intros; forward_reason.
                  subst.
                  shatter us; shatter us'.
                  specialize (H9 (hlist_app h4 h3) h2).
                  specialize (H7 (hlist_app h1 h0) h).
                  specialize (H8 (hlist_app h1 h0)).
                  revert H9.
                  autorewrite_with_eq_rw.
                  rewrite <- hlist_app_assoc'.
                  subst. rewrite <- hlist_app_assoc.
                  intros. etransitivity; eauto.
                  etransitivity; [ | eassumption ].
                  eapply H8; clear H8.
                  repeat rewrite hlist_split_hlist_app. simpl.
                  split; [ | split; [ | split ] ].
                  reflexivity. 3: eassumption.
                  reflexivity.
                  eapply Heq_mapD_mapD_nil.
                  eapply Heq_mapD_weaken.
                  simpl.
                  instantiate (2:=
                                 snd (hlist_split (getVars c) tvs vs')).
                  rewrite hlist_app_hlist_split.
                  eassumption. } } }

            { rewrite rel_dec_neq_false.
              2: eauto with typeclass_instances.
              2:{ rewrite Hes_tus_len. subst base. rewrite <- app_length. omega. }
              subst base. rewrite Hes_tus_len.
              assert (length
                        (filter
                           (fun x : option expr =>
                              match x with
                              | Some _ => false
                              | None => true
                              end) es) = length tus').
              { clear - H4.
                induction H4; (** lemma **)
                  solve [ reflexivity | simpl; assumption | simpl; f_equal; assumption ]. }
              rewrite H3.
              rewrite <- app_length.
              eapply nth_error_get_hlist_nth_appR in H1; simpl in H1; forward_reason.
              eapply nth_error_get_hlist_nth_appR in H1; simpl in H1; forward_reason.
              replace (u - length (getUVars c) - length tus)
                 with (u - length (getUVars c ++ tus))
                   in *
                   by (rewrite app_length; clear; omega).
              2: rewrite app_length in H0; omega.
              2: rewrite app_length in H0; omega.
              clear H.
              generalize dependent (u - length (getUVars c ++ tus)).
              clear H0. clear u.
              clear Heqmlist_inst mlist_inst H3.
              assert (forall u,
                      nth_error_get_hlist_nth typD ts u =
                      Some (existT (fun t1 : typ => hlist typD ts -> typD t1) t0 x2) ->
                      nth_error mlist u = Some None ->
                      exists
                        eUD : exprT (getUVars c ++ tus' ++ types_after_instantiate ts mlist)
                                    (getVars c ++ tvs) (typD t0),
                        exprD (getUVars c ++ tus' ++ types_after_instantiate ts mlist)
                               (getVars c ++ tvs) t0
                               (lookup_compress mlist (length (getUVars c ++ tus')) u) = 
                        Some eUD /\
                        (forall (usa : hlist typD (getUVars c ++ tus))
                                (usc : hlist typD ts)
                                (usa' : hlist typD (getUVars c ++ tus'))
                                (usc' : hlist typD (types_after_instantiate ts mlist))
                                (vs' : hlist typD (getVars c ++ tvs)),
                            Forgetting mlist usc usc' ->
                            x2 usc = eUD match app_ass_trans _ _ _ in _ = t return hlist _ t with
                                         | eq_refl => hlist_app usa' usc'
                                         end vs')).
              { clear - ExprUVarOk_expr RTypeOk_typ.
                intro u.
                destruct (app_ass_trans (getUVars c) tus' (types_after_instantiate ts mlist)).
                generalize dependent (getUVars c ++ tus').
                revert mlist; revert x2; revert ts.
                induction u; simpl; intros.
                { destruct mlist; simpl in *.
                  - inversion H0.
                  - inversion H0; clear H0; subst.
                    destruct ts; simpl in *; try congruence.
                    inv_all; subst. subst.
                    destruct (exprD_exact_uvar l (types_after_instantiate ts mlist) (getVars c ++ tvs) t).
                    forward_reason.
                    eexists; split; eauto.
                    intros.
                    rewrite (hlist_eta usc').
                    rewrite H0. tauto. }
                { destruct mlist; simpl in *.
                  - inversion H0.
                  - destruct ts. simpl in *. try congruence.
                    simpl in H. forwardy. inv_all. subst. subst.
                    destruct o; simpl.
                    { specialize (IHu ts t1 mlist l H H0).
                      forward_reason. eauto. }
                    { specialize (IHu ts t1 mlist (l++t::nil) H H0).
                      forward_reason.
                      rewrite exprD_conv with (pfv:=eq_refl)(pfu:=eq_sym (app_ass_trans _ _ _)) in H1.
                      autorewrite_with_eq_rw_in H1. forwardy.
                      inv_all; subst.
                      rewrite app_length in H1. simpl in H1.
                      rewrite Plus.plus_comm in H1.
                      eexists; split; eauto.
                      intros. destruct H3.
                      erewrite (H2 usa (hlist_tl usc) (hlist_app usa' (Hcons (hlist_hd usc') Hnil)) _ vs') by eauto.
                      clear.
                      autorewrite_with_eq_rw.
                      f_equal. rewrite hlist_app_assoc.
                      autorewrite_with_eq_rw. simpl. rewrite (hlist_eta usc').
                      reflexivity. } } }
              { clear - H H8 H7.
                intros. eapply H in H1; eauto.
                forward_reason.
                eexists; split; eauto.
                intros.
                rewrite <- (hlist_app_hlist_split _ _ us).
                rewrite H7; clear H7.
                rewrite <- (hlist_app_hlist_split _ _ (snd (hlist_split _ _ us))).
                rewrite H8; clear H8.
                specialize (H1 (hlist_app (fst (hlist_split _ _ us))
                                          (fst (hlist_split _ _ (snd (hlist_split _ _ us)))))
                               (snd (hlist_split _ _ (snd (hlist_split _ _ us))))
                               (hlist_app (fst (hlist_split _ _ us'))
                                          (fst (hlist_split _ _ (snd (hlist_split _ _ us')))))
                               (snd (hlist_split _ _ (snd (hlist_split _ _ us')))) vs').
                forward_reason. rewrite H1.
                clear. rewrite <- hlist_app_assoc'.
                rewrite hlist_app_hlist_split; simpl.
                rewrite hlist_app_hlist_split; simpl. reflexivity. } } }
          { intros. rewrite H3. eexists; split; eauto.
            clear. intros; intuition. subst. reflexivity. }
          { destruct H1.
            eexists; split; eauto.
            intros.
            specialize (H3 (hlist_app _us (hlist_app us us_))
                           vs
                           (hlist_app _us' (hlist_app us' us_'))
                           vs Hnil).
            simpl in *.
            eapply H3; clear H3.
            repeat (rewrite hlist_split_hlist_app; simpl).
            tauto. } }
        { destruct H9. subst ts'.
          assert (Heq_types_after :
                    types_after_instantiate ts mlist = types_after_instantiate ts mlist_inst).
          { subst mlist_inst.
            symmetry. eapply types_after_instantiate_map_fmap. }
          destruct Heq_types_after.
          destruct (H3 _ H9) as [ ? [ HgoalD Hres ] ]; clear H3.
          rewrite goalD_conv
             with (pfu:=app_ass_trans _ _ _)
                  (pfv:=eq_refl) in HgoalD.
          autorewrite_with_eq_rw_in HgoalD.
          replace (length (getUVars c ++ tus ++ ts))
             with (length ts + length (getUVars c ++ tus))
               in HgoalD by (repeat rewrite app_length; omega).
          forwardy.
          rewrite H3 in H5; clear H3.
          inversion H5; clear H5.
          eexists; split; eauto.
          clear H3 x4 H12.
          intros.
          eapply H13 in H12; try reflexivity.
          apply Quant._exists_sem in H12.
          destruct H12.
          destruct (H10 _us _us (hlist_app _vs vs) us us' x4); clear H10.
          { rewrite hlist_split_hlist_app. split; eauto. }
          { eapply (fun U U' => Heq_mapD_weaken U U' Hnil).
            eapply Heq_mapD_mapD_nil; eauto. }
          apply Quant._exists_sem.
          exists x5.
          rewrite H7; clear H7.
          inv_all. subst.
          autorewrite_with_eq_rw.
          rewrite hlist_app_assoc.
          autorewrite with eq_rw.
          clear H0 H9.
          destruct H14; split; auto.
          eapply Hres; eauto.
          autorewrite_with_eq_rw.
          rewrite <- hlist_app_assoc.
          tauto. } }

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
          eapply instantiate_do_instantiate_propD_sound in H3; eauto.
          forward_reason.
          generalize (@GHyp_do_solved_respects typ expr _ _ _ _ _ _ _ H).
          unfold EqGoal; simpl. intros.
          red in H6.
          destruct (H6 (minify_goal es (length (getUVars c ++ tus)) g) (minify_goal es (length (getUVars c ++ tus)) g)); clear H6.
          { clear. split; eauto. reflexivity.
            apply Option.Reflexive_Roption.
            eapply Reflexive_RexprT. eauto with typeclass_instances. }
          revert H8; simpl.
          eapply H2 in H5; clear H2; eauto.
          forward_reason.
          Cases.rewrite_all_goal.
          intros. inversion H8; clear H8; subst.
          eexists; split; eauto.
          intros.
          eapply (H5 _us _vs vs us us'); clear H5; eauto.
          eapply H10; try reflexivity. eauto.
          eapply H3; eauto. } }

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
        specialize (H3 _ _ _ H8 Hsubst Hes_tus_len H7).
        specialize (H5 _ _ _ H6 Hsubst Hes_tus_len H7).
        forward_reason.
        subst g'.
        destruct (@GConj_GConj_ typ expr _ _ _ (getUVars c ++ tus') (getVars c ++ tvs)
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
        generalize (H9 _us _vs vs us us' H13 H15); clear H9.
        generalize (H10 _us _vs _ _ _ H13 H15); clear H10.
        intros.
        eapply H14 in H16; try reflexivity.
        split.
        { eapply H9; eauto. tauto. }
        { eapply H10; eauto. tauto. } }

      { (* Goal *)
        intros. subst g'. simpl.
        split.
        { constructor. }
        simpl in *. intros.
        eapply instantiate_do_instantiate_propD_sound in H; eauto.
        forward_reason.
        eexists; split; eauto.
        intros.
        eapply H2; eauto. }

      { (* Solved *)
        intros; clear base_is_nus; subst.
        split; [ constructor | ].
        intros; inv_all; subst.
        simpl. eexists; split; eauto. }
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
    rewrite <- (app_nil_r_trans (getVars ctx)) in H.
    destruct (@minify_goal_sound_lem (length (getUVars ctx)) _ s eq_refl H0 g nil nil nil nil _ eq_refl H).
    split; auto.
    split.
    { clear - H1. repeat rewrite app_nil_r_trans in H1. assumption. }
    forward.
    rewrite goalD_conv with (pfu:=app_nil_r_trans _) (pfv:=eq_refl) in H4.
    autorewrite_with_eq_rw_in H4.
    forward.
    destruct (@pctxD_substD  _ _ _ _ _ _ _ _ _ _ H0 H3); forward_reason.
    rewrite goalD_conv with (pfv:=app_nil_r_trans _) (pfu:=eq_refl) in H4.
    autorewrite_with_eq_rw_in H4.
    forwardy.
    specialize (H2 _ _ _ H4 H6 eq_refl (@MD_nil_nil _ _ _)).
    forward_reason.
    inv_all; subst.
    rewrite goalD_conv with (pfu:=app_nil_r_trans _) (pfv:=eq_refl).
    autorewrite_with_eq_rw.
    cutrewrite (minify_goal (length (getUVars ctx)) s nil (length (getUVars ctx)) g = minify_goal (length (getUVars ctx)) s nil (length (getUVars ctx ++ nil)) g).
    { rewrite goalD_conv with (pfu:=eq_refl) (pfv:=app_nil_r_trans _).
      autorewrite_with_eq_rw.
      rewrite H2.
      split; [ reflexivity | ].
      intros. gather_facts.
      eapply Pure_pctxD; eauto. clear - H9.
      intros. specialize (H9 us vs Hnil Hnil _ eq_refl H).
      revert H0. autorewrite_with_eq_rw.
      repeat rewrite <- hlist_app_nil_r. eapply H9. }
    { f_equal. rewrite app_nil_r_trans. reflexivity. }
  Qed.

End parameterized.

Hint Opaque MINIFY : typeclass_instances.
Typeclasses Opaque MINIFY.

Arguments MINIFY {typ expr _ _ _} _ _ _ _ {_} _ _.
