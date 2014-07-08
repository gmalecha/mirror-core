Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprDI.

Set Implicit Arguments.
Set Strict Implicit.

Module Make (ED : ExprDenote).

  Hint Rewrite @ED.exprD'_Var @ED.exprD'_UVar @ED.exprD'_Inj @ED.exprD'_Abs @ED.exprD'_App using (eauto with typeclass_instances) : exprD_rw.

  Section with_types.
    Context {typ : Type}.
    Context {RType_typD : RType typ}.
    Context {Typ2_Fun : Typ2 _ Fun}.
    Context {func : Type}.
    Context {RSym_func : RSym func}.

    (** Reasoning principles **)
    Context {RTypeOk_typD : RTypeOk}.
    Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.
    Context {RSymOk_func : RSymOk RSym_func}.

    Local Instance RelDec_eq_typ : RelDec (@eq typ) :=
    { rel_dec := fun a b => match type_cast nil a b with
                              | Some _ => true
                              | None => false
                            end }.

    Local Instance RelDecCorrect_eq_typ : @RelDec_Correct _ (@eq typ) _.
    Proof.
      constructor. split; intros.
      { generalize (@type_cast_total _ _ _ nil x y). unfold rel_dec in H.
        simpl in *.
        destruct (type_cast nil x y). auto. congruence. }
      { subst. unfold rel_dec; simpl. rewrite type_cast_refl; auto. }
    Qed.

    Theorem exprD'_ind
    : (*@RTypeOk _ -> Typ2Ok Typ2_Fun -> RSymOk RSym_func -> *)
      forall (P : forall ts tus tvs, _ -> forall t, option (ED.OpenT _ tus tvs (typD ts t)) -> Prop) ts tus
        (Hnone : forall tvs e t,
                   ED.exprD' ts tus tvs t e = None ->
                   P ts tus tvs e t None)
        (Hvar : forall tvs v t t' get (pf : Rty ts t t'),
                  nth_error_get_hlist_nth _ tvs v = Some (@existT _ _ t' get) ->
                  P ts tus tvs (Var v) t
                    (Some (Relim (ED.OpenT ts tus tvs) pf (fun _ (vs : hlist _ tvs) => get vs))))
        (Huvar : forall tvs u t t' get (pf : Rty ts t t'),
                   nth_error_get_hlist_nth _ tus u = Some (@existT _ _ t' get) ->
                   P ts tus tvs (UVar u) t
                     (Some (Relim (ED.OpenT ts tus tvs) pf ((fun us _ => get us)))))
        (Hinj : forall tvs i t t' (pf : typeof_sym i = Some t)
                (pf' : Rty ts t' t),
                  P ts tus tvs (Inj i) t'
                    (Some (Relim (ED.OpenT ts tus tvs) pf' (fun _ _ =>
                             match pf in _ = t
                                   return match t with
                                            | Some t => typD ts t
                                            | None => unit
                                          end with
                               | eq_refl => symD ts i
                             end))))
        (Happ : forall tvs d r f x fval xval,
                  ED.typeof_expr ts tus tvs x = Some d ->
                  P ts tus tvs f (typ2 d r) (Some fval) ->
                  P ts tus tvs x d (Some xval) ->
                  P ts tus tvs (App f x) r
                    (Some (ED.Open_App fval xval)))
        (Habs : forall tvs d r e fval,
                  P ts tus (d :: tvs) e r (Some fval) ->
                  P ts tus tvs (Abs d e) (typ2 d r) (Some (ED.Open_Abs fval))),
        forall tvs e t,
        P ts tus tvs e t (ED.exprD' ts tus tvs t e).
    Proof.
      intros P ts tus Pnone Hvar Huvar Hinj Happ Habs tvs e; revert tvs.
      generalize (fun tvs => Pnone tvs e). intro.
      induction e;
      intros; generalize (H tvs t);
      autorewrite with exprD_rw in *; simpl in *;
      repeat match goal with
               | |- context [ match ?X with _ => _ end ] =>
                 (consider X; intros; auto); [ ]
             end.
      { subst. clear Happ Habs Huvar Hinj Pnone.
        specialize (@Hvar _ _ _ _ _ (Rsym r) H1).
        unfold ED.Rcast_val, ED.Rcast, Relim in *.
        generalize dependent (P ts tus tvs (Var v) t); clear.
        destruct r.
        auto. }
      { clear Habs Happ Huvar Hvar.
        unfold ED.funcAs in *.
        specialize (Hinj tvs f).
        generalize dependent (symD ts f).
        destruct (typeof_sym f); intros.
        { forward. specialize (Hinj _ t eq_refl (Rsym r)).
          generalize dependent (P ts tus tvs (Inj f) t).
          destruct r.
          simpl. unfold ED.Rcast in H0. simpl in H0.
          inv_all; subst. auto. }
        { exfalso; congruence. } }
      { clear Habs Hinj Huvar Hvar.
        eapply Happ; eauto.
        rewrite <- H1. auto.
        rewrite <- H2. auto. }
      { clear Hinj Huvar Hvar Happ.
        destruct (@typ2_match_case _ _ Fun _ _ ts t0).
        { specialize (H tvs t0). autorewrite with exprD_rw in *.
          (do 3 destruct H0); rewrite H0 in *; clear H0.
          consider (type_cast ts x t); intros.
          { specialize (fun H => IHe H (t :: tvs) x0).
            consider (ED.exprD' ts tus (t :: tvs) x0 e); intros.
            { eapply Habs in IHe; eauto.
              revert IHe. unfold ED.Open_Abs.
              destruct r.
              match goal with
                | |- _ _ _ _ _ _ (Some (match ?X with _ => _ end _)) ->
                     _ _ _ _ _ _ (Relim _ _ match ?Y with _ => _ end) =>
                  change Y with X ; generalize X
              end.
              clear H2. destruct x1.
              simpl. generalize (P ts tus tvs (Abs x e) t0).
              destruct e0. auto. }
            { match goal with
                | |- context [ match ?X with _ => _ end ] =>
                  generalize dependent X
              end.
              destruct x1. simpl.
              intros. rewrite eq_option_eq. eapply H3.
              clear. rewrite eq_option_eq. reflexivity. } }
          { clear - H0.
            match goal with
              | |- context [ match ?X with _ => _ end ] =>
                generalize dependent X
            end.
            destruct x1. simpl.
            intros. rewrite eq_option_eq. apply H0.
            rewrite eq_option_eq. reflexivity. } }
        { specialize (H tvs t0). autorewrite with exprD_rw in H.
          rewrite H0 in *. intros; apply H. reflexivity. } }
      { subst. clear Happ Habs Hvar Hinj Pnone.
        specialize (@Huvar tvs _ _ _ _ (Rsym r) H1).
        unfold ED.Rcast_val, ED.Rcast, Relim in *.
        generalize dependent (P ts tus tvs (UVar u) t); clear.
        destruct r.
        auto. }
    Qed.

    Theorem exprD'_ind_with
    : (*@RTypeOk _ -> Typ2Ok Typ2_Fun -> RSymOk RSym_func -> *)
      forall (P : forall ts tus tvs, _ -> forall t, option (ED.OpenT _ tus tvs (typD ts t)) -> Prop) ts tus
        (Hnone : forall tvs e t,
                   ED.exprD' ts tus tvs t e = None ->
                   P ts tus tvs e t None)
        (Hvar : forall tvs v t t' get (pf : Rty ts t t'),
                  nth_error_get_hlist_nth _ tvs v = Some (@existT _ _ t' get) ->
                  P ts tus tvs (Var v) t
                    (Some (Relim (ED.OpenT ts tus tvs) pf (fun _ (vs : hlist _ tvs) => get vs))))
        (Huvar : forall tvs u t t' get (pf : Rty ts t t'),
                   nth_error_get_hlist_nth _ tus u = Some (@existT _ _ t' get) ->
                   P ts tus tvs (UVar u) t
                     (Some (Relim (ED.OpenT ts tus tvs) pf ((fun us _ => get us)))))
        (Hinj : forall tvs i t t' (pf : typeof_sym i = Some t)
                (pf' : Rty ts t' t),
                  P ts tus tvs (Inj i) t'
                    (Some (Relim (ED.OpenT ts tus tvs) pf' (fun _ _ =>
                             match pf in _ = t
                                   return match t with
                                            | Some t => typD ts t
                                            | None => unit
                                          end with
                               | eq_refl => symD ts i
                             end))))
        (Happ : forall tvs d r f x fval xval,
                  ED.typeof_expr ts tus tvs x = Some d ->
                  P ts tus tvs f (typ2 d r) (Some fval) ->
                  P ts tus tvs x d (Some xval) ->
                  P ts tus tvs (App f x) r
                    (Some (ED.Open_App fval xval)))
        (Habs : forall tvs d r e fval,
                  P ts tus (d :: tvs) e r (Some fval) ->
                  P ts tus tvs (Abs d e) (typ2 d r) (Some (ED.Open_Abs fval))),
        forall tvs e t,
        P ts tus tvs e t (ED.exprD' ts tus tvs t e).
    Proof.
      intros P ts tus ? ? ? ? ? ? tvs e t.
      cut (ED.exprD' ts tus tvs t e = ED.exprD' ts tus tvs t e /\
           P ts tus tvs e t (ED.exprD' ts tus tvs t e)).
      { intuition. }
      refine (@exprD'_ind (fun ts tus tvs e t val =>
                           ED.exprD' ts tus tvs t e = val /\
                           P ts tus tvs e t val) ts tus _ _ _ _ _ _ tvs e t); eauto.
      { intros; split; eauto.
        autorewrite with exprD_rw.
        rewrite H. simpl.
        destruct pf. rewrite type_cast_refl; eauto. }
      { intros; split; eauto.
        autorewrite with exprD_rw.
        rewrite H. simpl.
        destruct pf. rewrite type_cast_refl; eauto. }
      { intros; split; eauto.
        autorewrite with exprD_rw.
        unfold ED.funcAs.
        generalize (symD ts i).
        rewrite pf. destruct pf'. rewrite type_cast_refl; eauto. }
      { intros. destruct H0. destruct H1.
        split; eauto.
        autorewrite with exprD_rw.
        Cases.rewrite_all_goal. simpl.
        rewrite H0. rewrite H1. reflexivity. }
      { intros. destruct H. split; eauto.
        autorewrite with exprD_rw.
        rewrite typ2_match_zeta; eauto.
        rewrite type_cast_refl; eauto. rewrite H.
        simpl. unfold ED.Open_Abs, ED.OpenT, ResType.OpenT.
        rewrite eq_option_eq.
        repeat rewrite eq_Arr_eq. repeat rewrite eq_Const_eq.
        reflexivity. }
    Qed.

    Theorem typeof_expr_weaken
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall ts tus tvs e t tus' tvs',
        ED.typeof_expr ts tus tvs e = Some t ->
        ED.typeof_expr ts (tus ++ tus') (tvs ++ tvs') e = Some t.
    Proof.
      intros ? ? ? ts tus tvs e; revert tvs.
      induction e; simpl; intros; eauto using ListNth.nth_error_weaken.
      { forward.
        erewrite IHe1; eauto.
        erewrite IHe2; eauto. }
      { forward. change (t :: tvs ++ tvs') with ((t :: tvs) ++ tvs').
        erewrite IHe; eauto. }
    Qed.

    Theorem exprD'_weaken
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall ts tus tvs (e : expr typ func) t val tus' tvs',
        ED.exprD' ts tus tvs t e = Some val ->
        exists val',
          ED.exprD' ts (tus ++ tus') (tvs ++ tvs') t e = Some val' /\
          forall us vs us' vs',
            val us vs = val' (hlist_app us us') (hlist_app vs vs').
    Proof.
      intros ? ? ? ts tus tvs e t val tus' tvs'.
      revert e t val.
      refine (@exprD'_ind 
                          (fun ts tus tvs e t val =>
                             forall val'',
                               val = Some val'' ->
                               exists val' : ED.OpenT ts (tus ++ tus') (tvs ++ tvs') (typD ts t),
                                 ED.exprD' ts (tus ++ tus') (tvs ++ tvs') t e = Some val' /\
                                 (forall (us : hlist (typD ts) tus) (vs : hlist (typD ts) tvs)
                                         (us' : hlist (typD ts) tus') (vs' : hlist (typD ts) tvs'),
                                    val'' us vs = val' (hlist_app us us') (hlist_app vs vs')))
                          _ _ _ _ _ _ _ _ _).
      { congruence. }
      { intros; inv_all; subst.
        autorewrite with exprD_rw in *; simpl.
        eapply nth_error_get_hlist_nth_weaken in H2.
        simpl in *. destruct H2 as [ ? [ ? ? ] ].
        rewrite H2.
        destruct pf. rewrite type_cast_refl; eauto. }
      { intros; inv_all; subst.
        autorewrite with exprD_rw in *; simpl.
        eapply nth_error_get_hlist_nth_weaken in H2.
        simpl in *. destruct H2 as [ ? [ ? ? ] ].
        rewrite H2.
        destruct pf. rewrite type_cast_refl; eauto.
        simpl. eexists; split; eauto. intros.
        eapply H3. }
      { intros; inv_all; subst.
        autorewrite with exprD_rw. simpl.
        unfold ED.funcAs.
        generalize (symD ts i). rewrite pf.
        destruct pf'.
        rewrite type_cast_refl; eauto. simpl.
        eexists; split; eauto. }
      { simpl; intros.
        specialize (H3 _ eq_refl).
        specialize (H4 _ eq_refl).
        forward_reason; inv_all; subst.
        autorewrite with exprD_rw. simpl.
        erewrite typeof_expr_weaken by eauto.
        rewrite H4. rewrite H3.
        eexists; split; eauto.
        revert H6 H7. clear.
        unfold ED.Open_App. intros.

        repeat rewrite eq_Arr_eq.
        repeat rewrite eq_Const_eq.
        rewrite <- H6.
        clear - H7.
        unfold ED.OpenT, ResType.OpenT.
        repeat (rewrite eq_Const_eq || rewrite eq_Arr_eq).
        rewrite <- H7. reflexivity. }
      { intros. forward_reason; inv_all; subst.
        specialize (H2 _ eq_refl).
        destruct H2 as [ ? [ ? ? ] ].
        autorewrite with exprD_rw. simpl.
        rewrite typ2_match_zeta; eauto.
        rewrite type_cast_refl; eauto.
        simpl in *.
        rewrite H2.
        rewrite eq_option_eq. eexists; split; eauto.
        intros.
        clear - H3.
        unfold ED.Open_Abs, ED.OpenT, ResType.OpenT.
        repeat (rewrite eq_Const_eq || rewrite eq_Arr_eq).
        match goal with
          | |- match ?X with _ => _ end = match ?Y with _ => _ end =>
            change Y with X ; generalize X
        end.
        destruct e. eapply FunctionalExtensionality.functional_extensionality.
        intros.
        erewrite H3. reflexivity. }
    Qed.

    Theorem typeof_expr_exprD'
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall ts tus tvs e t,
        ED.typeof_expr ts tus tvs e = Some t ->
        exists val,
          ED.exprD' ts tus tvs t e = Some val.
    Proof.
      intros ? ? ? ts tus tvs e; revert tvs; induction e; simpl; intros;
      autorewrite with exprD_rw; simpl.
      { consider (nth_error_get_hlist_nth (typD ts) tvs v); intros.
        { destruct s.
          eapply nth_error_get_hlist_nth_Some in H3. simpl in *.
          destruct H3. rewrite x0 in H2. inv_all; subst.
          rewrite type_cast_refl; eauto. }
        { rewrite nth_error_get_hlist_nth_None in H3. congruence. } }
      { unfold ED.funcAs.
        generalize (symD ts f). rewrite H2.
        rewrite type_cast_refl; eauto.
        simpl. eauto. }
      { forward.
        eapply IHe1 in H2.
        eapply IHe2 in H3.
        forward_reason.
        unfold ED.type_of_apply in H4.
        destruct (typ2_match_case (F := Fun)  ts t0).
        { forward_reason. rewrite H5 in H4; clear H5.
          unfold Relim in H4.
          rewrite eq_Const_eq in H4.
          rewrite H3.
          generalize dependent (typ2_cast ts x1 x2).
          destruct e. simpl; intros; forward.
          inv_all; subst. red in r. red in x3. subst.
          rewrite H2. eauto. }
        { exfalso. rewrite H5 in H4. congruence. } }
      { forward. inv_all; subst.
        rewrite typ2_match_zeta; eauto.
        rewrite type_cast_refl; eauto.
        eapply IHe in H2. forward_reason.
        rewrite H2.
        destruct (eq_sym (typ2_cast ts t t1)). eauto. }
      { consider (nth_error_get_hlist_nth (typD ts) tus u); intros.
        { destruct s.
          eapply nth_error_get_hlist_nth_Some in H3. simpl in *.
          destruct H3. rewrite x0 in H2. inv_all; subst.
          rewrite type_cast_refl; eauto. }
        { rewrite nth_error_get_hlist_nth_None in H3. congruence. } }
    Qed.

    Theorem exprD'_single_type
    : (*@RTypeOk _ -> Typ2Ok Typ2_Fun -> RSymOk RSym_func -> *)
      forall ts tus tvs e t t' val val',
        ED.exprD' ts tus tvs t e = Some val ->
        ED.exprD' ts tus tvs t' e = Some val' ->
        exists pf : Rty ts t t',
          Relim (ED.OpenT ts tus tvs) pf val' = val.
    Proof.
      intros ts tus tvs.
      refine (@exprD'_ind
                          (fun ts tus tvs e t val'' =>
                             forall t' val val',
                               val'' = Some val ->
                               ED.exprD' ts tus tvs t' e = Some val' ->
                               exists pf : Rty ts t t',
                                 Relim (ED.OpenT ts tus tvs) pf val' = val)
                          _ _ _ _ _ _ _ _ _).
      { congruence. }
      { intros; inv_all; subst.
        autorewrite with exprD_rw in *; simpl in *.
        rewrite H in *.
        destruct (type_cast ts t' t'0).
        { inv_all; subst. destruct r. destruct pf. exists (Rrefl _ _).
          reflexivity. }
        { congruence. } }
      { intros; inv_all; subst.
        autorewrite with exprD_rw in *; simpl in *.
        rewrite H in *.
        destruct (type_cast ts t' t'0).
        { inv_all; subst. destruct r. destruct pf. exists (Rrefl _ _).
          reflexivity. }
        { congruence. } }
      { intros; inv_all; subst.
        autorewrite with exprD_rw in *; simpl in *.
        unfold ED.funcAs in *.
        generalize dependent (symD ts i).
        rewrite pf.
        destruct pf'.
        destruct (type_cast ts t' t'0).
        { intros. exists r.
          destruct r. simpl in *. inv_all; subst. reflexivity. }
        { congruence. } }
      { intros; inv_all; subst.
        autorewrite with exprD_rw in *; simpl in *.
        forward; inv_all; subst.
        eapply (H0 _ _ _ eq_refl) in H3.
        eapply (H1 _ _ _ eq_refl) in H4.
        forward_reason.
        destruct (typ2_inj _ _ _ _ x1).
        exists H5. destruct H5. simpl.
        subst. clear.
        f_equal. clear. generalize dependent (typ2 d r).
        (** NOTE(gmalecha): relying on [Rty = eq] **)
        unfold Rty. uip_all'. reflexivity.
        red in x0. uip_all'. reflexivity. }
      { intros; inv_all; subst.
        autorewrite with exprD_rw in *; simpl in *.
        forward; inv_all; subst.
        destruct (typ2_match_case ts t').
        { destruct H0 as [ ? [ ? [ ? ? ] ] ].
          rewrite H0 in *; clear H0.
          destruct (type_cast ts x d).
          { destruct r0.
            consider (ED.exprD' ts tus (x :: tvs0) x0 e); intros.
            { eapply H in H0; clear H; eauto.
              destruct H0. destruct x2.
              subst. exists (Rsym x1). unfold ED.Open_Abs.
              generalize dependent (typ2_cast ts x r).
              destruct x1. simpl; intros.
              rewrite eq_option_eq in H1.
              inv_all; subst.
              rewrite eq_Arr_eq; rewrite eq_Const_eq. reflexivity. }
            { exfalso.
              generalize dependent (typ2_cast ts x x0). clear.
              destruct x1. destruct e. simpl; congruence. } }
          { exfalso.
            generalize dependent (typ2_cast ts x x0). clear.
            destruct x1. destruct e. simpl; congruence. } }
        { rewrite H0 in *. congruence. } }
    Qed.

    Theorem exprD'_typeof_expr
    : (*@RTypeOk _ -> Typ2Ok Typ2_Fun -> RSymOk RSym_func -> *)
      forall ts tus tvs e t,
        ED.typeof_expr ts tus tvs e = Some t <->
        exists val,
          ED.exprD' ts tus tvs t e = Some val.
    Proof.
      intros ts tus tvs e; revert tvs.
      induction e; simpl; intros; autorewrite with exprD_rw; simpl.
      { split; intro.
        { consider (nth_error_get_hlist_nth (typD ts) tvs v); intros.
          { destruct s. eapply nth_error_get_hlist_nth_Some in H0.
            simpl in *. destruct H0.
            rewrite x0 in H. inv_all; subst.
            rewrite type_cast_refl; eauto. }
          { rewrite nth_error_get_hlist_nth_None in H0. congruence. } }
        { forward_reason. forward; inv_all; subst.
          destruct r. eapply nth_error_get_hlist_nth_Some in H0.
          destruct H0. assumption. } }
      { split; intros.
        { unfold ED.funcAs. generalize (symD ts f).
          rewrite H. rewrite type_cast_refl; eauto.
          simpl. eauto. }
        { forward_reason; forward.
          unfold ED.funcAs in H.
          generalize dependent (symD ts f).
          destruct (typeof_sym f); try congruence.
          intros. forward. } }
      { split; intros.
        { forward.
          eapply IHe1 in H. eapply IHe2 in H0.
          forward_reason.
          unfold ED.type_of_apply in H1.
          destruct (typ2_match_case ts t0).
          { destruct H2 as [ ? [ ? [ ? ? ] ] ].
            rewrite H2 in H1; clear H2.
            rewrite H0. generalize dependent (typ2_cast ts x1 x2).
            red in x3. subst.
            destruct e. simpl; intros; forward.
            destruct r. inv_all; subst. rewrite H. eauto. }
          { rewrite H2 in H1. congruence. } }
        { forward_reason; forward; inv_all; subst.
          cutrewrite (ED.typeof_expr ts tus tvs e1 = Some (typ2 t0 t)).
          { unfold ED.type_of_apply.
            rewrite typ2_match_zeta; eauto.
            rewrite type_cast_refl; eauto.
            rewrite eq_Const_eq. reflexivity. }
          { rewrite IHe1. eauto. } } }
      { split; intros; forward; inv_all; subst.
        { rewrite typ2_match_zeta; eauto.
          rewrite type_cast_refl; eauto.
          rewrite IHe in H. forward_reason.
          rewrite H. forward. eauto. }
        { forward_reason.
          destruct (typ2_match_case ts t0).
          { destruct H0 as [ ? [ ? [ ? ? ] ] ].
            rewrite H0 in H; clear H0.
            generalize dependent (typ2_cast ts x0 x1).
            red in x2. subst. simpl; intros.
            consider (type_cast ts x0 t); intros.
            { specialize (IHe (t :: tvs) x1).
              destruct (ED.exprD' ts tus (t :: tvs) x1 e).
              { destruct IHe. rewrite H2; eauto. destruct r. auto. }
              { exfalso. clear - H0. destruct e0. simpl in *; congruence. } }
            { exfalso; clear - H0. destruct e0. simpl in *; congruence. } }
          { rewrite H0 in H. congruence. } } }
      { split; intro.
        { consider (nth_error_get_hlist_nth (typD ts) tus u); intros.
          { destruct s. eapply nth_error_get_hlist_nth_Some in H0.
            simpl in *. destruct H0.
            rewrite x0 in H. inv_all; subst.
            rewrite type_cast_refl; eauto. }
          { rewrite nth_error_get_hlist_nth_None in H0. congruence. } }
        { forward_reason. forward; inv_all; subst.
          destruct r. eapply nth_error_get_hlist_nth_Some in H0.
          destruct H0. assumption. } }
    Qed.

    Theorem exprD'_type_cast
    : @RTypeOk typ _ -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall ts tus tvs e t,
        ED.exprD' ts tus tvs t e =
        match ED.typeof_expr ts tus tvs e with
          | None => None
          | Some t' =>
            match @type_cast _ _ ts t' t with
              | None => None
              | Some cast =>
                match ED.exprD' ts tus tvs t' e with
                  | None => None
                  | Some x =>
                    Some (fun us gs => ED.Rcast (fun x => x) cast (x us gs))
                end
            end
        end.
    Proof.
      intros.
      consider (ED.typeof_expr ts tus tvs e); intros.
      { consider (type_cast ts t0 t); intros.
        { symmetry.
          erewrite ED.exprD'_respects with (pf := Rsym r); eauto.
          clear. destruct r.
          destruct (ED.exprD' ts tus tvs t0 e); reflexivity. }
        { consider (ED.exprD' ts tus tvs t e); auto; intros.
          exfalso.
          rewrite exprD'_typeof_expr in H2.
          destruct H2.
          destruct (exprD'_single_type H2 H4).
          destruct x0. rewrite type_cast_refl in H3; eauto.
          congruence. } }
      { consider (ED.exprD' ts tus tvs t e); auto.
        intros. exfalso.
        cut (ED.typeof_expr ts tus tvs e = Some t).
        congruence.
        rewrite exprD'_typeof_expr. eauto. }
    Qed.

  End with_types.
End Make.
