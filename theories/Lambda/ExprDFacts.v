Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.AbsAppI.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprDI.

Require Import MirrorCore.Util.Compat.

Set Implicit Arguments.
Set Strict Implicit.

Module Make (ED : ExprDenote).

  Hint Rewrite @ED.lambda_exprD_Var @ED.lambda_exprD_UVar @ED.lambda_exprD_Inj @ED.lambda_exprD_Abs @ED.lambda_exprD_App using (eauto with typeclass_instances) : exprD_rw.

  Section with_types.
    Context {typ : Set}.
    Context {RType_typD : RType typ}.
    Context {Typ2_Fun : Typ2 _ RFun}.
    Context {func : Set}.
    Context {RSym_func : RSym func}.

    (** Reasoning principles **)
    Context {RTypeOk_typD : RTypeOk}.
    Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.
    Context {RSymOk_func : RSymOk RSym_func}.

    Local Instance RelDec_eq_typ : RelDec (@eq typ) :=
    { rel_dec := fun a b => match type_cast a b with
                              | Some _ => true
                              | None => false
                            end }.

    Local Instance RelDecCorrect_eq_typ : @RelDec_Correct _ (@eq typ) _.
    Proof.
      constructor. split; intros.
      { generalize (@type_cast_total _ _ _ x y). unfold rel_dec in H.
        simpl in *.
        destruct (type_cast x y). auto. congruence. }
      { subst. unfold rel_dec; simpl. rewrite type_cast_refl; auto. }
    Qed.

    Theorem lambda_exprD_ind
    : (*@RTypeOk _ -> Typ2Ok Typ2_Fun -> RSymOk RSym_func -> *)
      forall (P : forall tus tvs, _ -> forall t, option (exprT tus tvs (typD t)) -> Prop) tus
        (Hnone : forall tvs e t,
                   ED.lambda_exprD tus tvs t e = None ->
                   P tus tvs e t None)
        (Hvar : forall tvs v t t' get (pf : Rty t t'),
                  nth_error_get_hlist_nth _ tvs v = Some (@existT _ _ t' get) ->
                  P tus tvs (Var v) t
                    (Some (Relim (exprT tus tvs) pf (fun _ (vs : hlist _ tvs) => get vs))))
        (Huvar : forall tvs u t t' get (pf : Rty t t'),
                   nth_error_get_hlist_nth _ tus u = Some (@existT _ _ t' get) ->
                   P tus tvs (UVar u) t
                     (Some (Relim (exprT tus tvs) pf ((fun us _ => get us)))))
        (Hinj : forall tvs i t t' (pf : typeof_sym i = Some t)
                (pf' : Rty t' t),
                  P tus tvs (Inj i) t'
                    (Some (Relim (exprT tus tvs) pf' (fun _ _ =>
                             match pf in _ = t
                                   return match t with
                                            | Some t => typD t
                                            | None => unit
                                          end with
                               | eq_refl => symD i
                             end))))
        (Happ : forall tvs d r f x fval xval,
                  ED.typeof_expr tus tvs x = Some d ->
                  P tus tvs f (typ2 d r) (Some fval) ->
                  P tus tvs x d (Some xval) ->
                  P tus tvs (App f x) r
                    (Some (exprT_App fval xval)))
        (Habs : forall tvs d r e fval,
                  P tus (d :: tvs) e r (Some fval) ->
                  P tus tvs (Abs d e) (typ2 d r) (Some (exprT_Abs fval))),
        forall tvs e t,
        P tus tvs e t (ED.lambda_exprD tus tvs t e).
    Proof.
      intros P tus Pnone Hvar Huvar Hinj Happ Habs tvs e; revert tvs.
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
        generalize dependent (P tus tvs (Var v) t); clear.
        destruct r.
        auto. }
      { clear Habs Happ Huvar Hvar.
        unfold symAs in *.
        specialize (Hinj tvs f).
        generalize dependent (symD f).
        destruct (typeof_sym f); intros.
        { forward. specialize (Hinj _ t eq_refl r).
          generalize dependent (P tus tvs (Inj f) t).
          destruct r.
          simpl. unfold ED.Rcast in H0. simpl in H0.
          inv_all; subst. auto. }
        { exfalso; congruence. } }
      { clear Habs Hinj Huvar Hvar.
        eapply Happ; eauto.
        rewrite <- H1. auto.
        rewrite <- H2. auto. }
      { clear Hinj Huvar Hvar Happ.
        destruct (@typ2_match_case _ _ RFun _ _ t0).
        { specialize (H tvs t0). autorewrite with exprD_rw in *.
          (do 3 destruct H0); rewrite H0 in *; clear H0.
          consider (type_cast x t); intros.
          { specialize (fun H => IHe H (t :: tvs) x0).
            consider (ED.lambda_exprD tus (t :: tvs) x0 e); intros.
            { eapply Habs in IHe; eauto.
              revert IHe. unfold exprT_Abs.
              destruct r.
              match goal with
                | |- _ _ _ _ _ (Some (match ?X with _ => _ end _)) ->
                     _ _ _ _ _ (Relim _ _ match ?Y with _ => _ end) =>
                  change Y with X ; generalize X
              end.
              clear H2. destruct x1.
              simpl. generalize (P tus tvs (Abs x e) t0).
              destruct e1. auto. }
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
        generalize dependent (P tus tvs (UVar u) t); clear.
        destruct r.
        auto. }
    Qed.

    Theorem lambda_exprD_ind_with
    : (*@RTypeOk _ -> Typ2Ok Typ2_Fun -> RSymOk RSym_func -> *)
      forall (P : forall tus tvs, _ -> forall t, option (exprT tus tvs (typD t)) -> Prop) tus
        (Hnone : forall tvs e t,
                   ED.lambda_exprD tus tvs t e = None ->
                   P tus tvs e t None)
        (Hvar : forall tvs v t t' get (pf : Rty t t'),
                  nth_error_get_hlist_nth _ tvs v = Some (@existT _ _ t' get) ->
                  P tus tvs (Var v) t
                    (Some (Relim (exprT tus tvs) pf (fun _ (vs : hlist _ tvs) => get vs))))
        (Huvar : forall tvs u t t' get (pf : Rty t t'),
                   nth_error_get_hlist_nth _ tus u = Some (@existT _ _ t' get) ->
                   P tus tvs (UVar u) t
                     (Some (Relim (exprT tus tvs) pf ((fun us _ => get us)))))
        (Hinj : forall tvs i t t' (pf : typeof_sym i = Some t)
                (pf' : Rty t' t),
                  P tus tvs (Inj i) t'
                    (Some (Relim (exprT tus tvs) pf' (fun _ _ =>
                             match pf in _ = t
                                   return match t with
                                            | Some t => typD t
                                            | None => unit
                                          end with
                               | eq_refl => symD i
                             end))))
        (Happ : forall tvs d r f x fval xval,
                  ED.typeof_expr tus tvs x = Some d ->
                  P tus tvs f (typ2 d r) (Some fval) ->
                  P tus tvs x d (Some xval) ->
                  P tus tvs (App f x) r
                    (Some (exprT_App fval xval)))
        (Habs : forall tvs d r e fval,
                  P tus (d :: tvs) e r (Some fval) ->
                  P tus tvs (Abs d e) (typ2 d r) (Some (exprT_Abs fval))),
        forall tvs e t,
        P tus tvs e t (ED.lambda_exprD tus tvs t e).
    Proof.
      intros P tus ? ? ? ? ? ? tvs e t.
      cut (ED.lambda_exprD tus tvs t e = ED.lambda_exprD tus tvs t e /\
           P tus tvs e t (ED.lambda_exprD tus tvs t e)).
      { intuition. }
      refine (@lambda_exprD_ind (fun tus tvs e t val =>
                           ED.lambda_exprD tus tvs t e = val /\
                           P tus tvs e t val) tus _ _ _ _ _ _ tvs e t); eauto.
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
        unfold symAs.
        generalize (symD i).
        rewrite pf. destruct pf'. rewrite type_cast_refl; eauto. }
      { intros. destruct H0. destruct H1.
        split; eauto.
        autorewrite with exprD_rw.
        Cases.rewrite_all_goal. reflexivity. }
      { intros. destruct H. split; eauto.
        autorewrite with exprD_rw.
        rewrite typ2_match_iota; eauto.
        rewrite type_cast_refl; eauto. rewrite H.
        simpl. unfold exprT_Abs.
        autorewrite with eq_rw.
        reflexivity. }
    Qed.

    Theorem typeof_expr_weaken
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall tus tvs e t tus' tvs',
        ED.typeof_expr tus tvs e = Some t ->
        ED.typeof_expr (tus ++ tus') (tvs ++ tvs') e = Some t.
    Proof.
      intros ? ? ? tus tvs e; revert tvs.
      induction e; simpl; intros; eauto using ListNth.nth_error_weaken.
      { forward.
        erewrite IHe1; eauto.
        erewrite IHe2; eauto. }
      { forward. change (t :: tvs ++ tvs') with ((t :: tvs) ++ tvs').
        erewrite IHe; eauto. }
    Qed.

    Theorem lambda_exprD_weaken
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall tus tvs (e : expr typ func) t val tus' tvs',
        ED.lambda_exprD tus tvs t e = Some val ->
        exists val',
          ED.lambda_exprD (tus ++ tus') (tvs ++ tvs') t e = Some val' /\
          forall us vs us' vs',
            val us vs = val' (hlist_app us us') (hlist_app vs vs').
    Proof.
      intros ? ? ? tus tvs e t val tus' tvs'.
      revert e t val.
      refine (@lambda_exprD_ind
                (fun tus tvs e t val =>
                   forall val'',
                     val = Some val'' ->
                     exists val' : exprT (tus ++ tus') (tvs ++ tvs') (typD t),
                       ED.lambda_exprD (tus ++ tus') (tvs ++ tvs') t e = Some val' /\
                       (forall (us : hlist typD tus) (vs : hlist typD tvs)
                               (us' : hlist typD tus') (vs' : hlist typD tvs'),
                           val'' us vs = val' (hlist_app us us') (hlist_app vs vs')))
                _ _ _ _ _ _ _ _).
      { congruence. }
      { intros; inv_all; subst.
        autorewrite with exprD_rw in *; simpl.
        eapply nth_error_get_hlist_nth_weaken in H1.
        simpl in *. destruct H1 as [ ? [ ? ? ] ].
        rewrite H1.
        destruct pf. rewrite type_cast_refl; eauto. }
      { intros; inv_all; subst.
        autorewrite with exprD_rw in *; simpl.
        eapply nth_error_get_hlist_nth_weaken in H1.
        simpl in *. destruct H1 as [ ? [ ? ? ] ].
        rewrite H1.
        destruct pf. rewrite type_cast_refl; eauto.
        simpl. eexists; split; eauto. intros.
        eapply H2. }
      { intros; inv_all; subst.
        autorewrite with exprD_rw. simpl.
        unfold symAs.
        generalize (symD i). rewrite pf.
        destruct pf'.
        rewrite type_cast_refl; eauto. }
      { simpl; intros.
        specialize (H3 _ eq_refl).
        specialize (H2 _ eq_refl).
        forward_reason; inv_all; subst.
        autorewrite with exprD_rw. simpl.
        erewrite typeof_expr_weaken by eauto.
        rewrite H2. rewrite H3.
        eexists; split; eauto.
        revert H5 H6. clear.
        unfold exprT_App. intros.
        autorewrite_with_eq_rw.
        rewrite <- H6.
        rewrite <- H5. reflexivity. }
      { intros. forward_reason; inv_all; subst.
        specialize (H1 _ eq_refl).
        destruct H1 as [ ? [ ? ? ] ].
        autorewrite with exprD_rw. simpl.
        rewrite typ2_match_iota; eauto.
        rewrite type_cast_refl; eauto.
        simpl in *.
        rewrite H1.
        rewrite eq_option_eq. eexists; split; eauto.
        intros.
        clear - H2.
        unfold exprT_Abs, exprT.
        autorewrite_with_eq_rw; simpl.
        match goal with
          | |- match ?X with _ => _ end = match ?Y with _ => _ end =>
            change Y with X ; generalize X
        end.
        destruct e. eapply FunctionalExtensionality.functional_extensionality.
        intros.
        erewrite H2. reflexivity. }
    Qed.

    Theorem typeof_expr_lambda_exprD
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall tus tvs e t,
        ED.typeof_expr tus tvs e = Some t ->
        exists val,
          ED.lambda_exprD tus tvs t e = Some val.
    Proof.
      intros ? ? ? tus tvs e; revert tvs; induction e; simpl; intros;
      autorewrite with exprD_rw; simpl.
      { consider (nth_error_get_hlist_nth typD tvs v); intros.
        { destruct s.
          eapply nth_error_get_hlist_nth_Some in H2. simpl in *.
          destruct H2. rewrite x0 in H1. inv_all; subst.
          rewrite type_cast_refl; eauto. }
        { rewrite nth_error_get_hlist_nth_None in H2. congruence. } }
      { unfold symAs.
        generalize (symD f). rewrite H1.
        rewrite type_cast_refl; eauto. }
      { forward.
        eapply IHe1 in H1.
        eapply IHe2 in H2.
        forward_reason.
        unfold ED.type_of_apply in H3.
        destruct (typ2_match_case (F := RFun)  t0).
        { forward_reason. rewrite H4 in H3; clear H4.
          unfold Relim in H3.
          rewrite eq_Const_eq in H3.
          rewrite H2.
          generalize dependent (typ2_cast x1 x2).
          destruct e. simpl; intros; forward.
          inv_all; subst. red in r. red in x3. subst.
          rewrite H1. eauto. }
        { exfalso. rewrite H4 in H3. congruence. } }
      { forward. inv_all; subst.
        rewrite typ2_match_iota; eauto.
        rewrite type_cast_refl; eauto.
        eapply IHe in H1. forward_reason.
        rewrite H1.
        destruct (eq_sym (typ2_cast t t1)). eauto. }
      { consider (nth_error_get_hlist_nth typD tus u); intros.
        { destruct s.
          eapply nth_error_get_hlist_nth_Some in H2. simpl in *.
          destruct H2. rewrite x0 in H1. inv_all; subst.
          rewrite type_cast_refl; eauto. }
        { rewrite nth_error_get_hlist_nth_None in H2. congruence. } }
    Qed.

    Theorem type_of_apply_Some
    : forall t u v (H : ED.type_of_apply t u = Some v),
        t = typ2 u v.
    Proof.
      intros.
      unfold ED.type_of_apply in H.
      destruct (typ2_match_case t) as [[a [b [pf H1]]] | H1].
      { unfold Rty in pf. subst.
        rewrite typ2_match_iota in H; [|apply _].
        unfold eq_sym in H.
        forward. }
      { specialize (H1 (fun _ => option typ)).
        specialize (H1 (fun d r => match type_cast d u with | Some _ => Some r | None => None end)).
        simpl in H1. specialize (H1 None). rewrite H in H1. congruence. }
    Qed.

    Theorem typeof_expr_App
    : forall tus tvs e1 e2 t,
        ED.typeof_expr tus tvs (App e1 e2) = Some t ->
        exists u,
             ED.typeof_expr tus tvs e1 = Some (typ2 u t)
          /\ ED.typeof_expr tus tvs e2 = Some u.
    Proof.
      simpl. intros; forward.
      eapply type_of_apply_Some in H1. subst.
      eauto.
    Qed.

    Theorem typeof_expr_Abs
    : forall tus tvs e t1 t,
        ED.typeof_expr tus tvs (Abs t1 e) = Some t ->
        exists t2, t = typ2 t1 t2 /\
             ED.typeof_expr tus (t1 :: tvs) e = Some t2.
    Proof.
      simpl. intros.
      forward. inv_all. subst. eauto.
    Qed.

    Theorem typeof_expr_Var
    : forall tus tvs v t,
        ED.typeof_expr tus tvs (Var v) = Some t ->
        nth_error tvs v = Some t.
    Proof.
      simpl; auto.
    Qed.

    Theorem typeof_expr_UVar
    : forall tus tvs v t,
        ED.typeof_expr tus tvs (UVar v) = Some t ->
        nth_error tus v = Some t.
    Proof.
      simpl; auto.
    Qed.

    Theorem typeof_expr_Inj
    : forall tus tvs (f : func) (t : typ),
        ED.typeof_expr tus tvs (Inj f) = Some t ->
        typeof_sym f = Some t.
    Proof.
      simpl; auto.
    Qed.

    Global Instance Injective_typeof_expr_Inj tus tvs (f : func) (t : typ)
    : Injective (ED.typeof_expr tus tvs (Inj f) = Some t) :=
    { result := typeof_sym f = Some t
    ; injection := @typeof_expr_Inj _ _ _ _ }.

    Global Instance Injective_typeof_expr_Var tus tvs v (t : typ)
    : Injective (ED.typeof_expr tus tvs (Var v) = Some t) :=
    { result := nth_error tvs v = Some t
    ; injection := @typeof_expr_Var _ _ _ _ }.

    Global Instance Injective_typeof_expr_UVar tus tvs v (t : typ)
    : Injective (ED.typeof_expr tus tvs (UVar v) = Some t) :=
    { result := nth_error tus v = Some t
    ; injection := @typeof_expr_UVar _ _ _ _ }.

    Global Instance Injective_typeof_expr_App tus tvs e1 e2 (t : typ)
    : Injective (ED.typeof_expr tus tvs (App e1 e2) = Some t) :=
    { result := _
    ; injection := @typeof_expr_App _ _ _ _ _ }.

    Global Instance Injective_typeof_expr_Abs tus tvs t1 e2 (t : typ)
    : Injective (ED.typeof_expr tus tvs (Abs t1 e2) = Some t) :=
    { result := _
    ; injection := @typeof_expr_Abs _ _ _ _ _ }.

    Theorem lambda_exprD_single_type
    : (*@RTypeOk _ -> Typ2Ok Typ2_Fun -> RSymOk RSym_func -> *)
      forall tus tvs e t t' val val',
        ED.lambda_exprD tus tvs t e = Some val ->
        ED.lambda_exprD tus tvs t' e = Some val' ->
        exists pf : Rty t t',
          Relim (exprT tus tvs) pf val' = val.
    Proof.
      intros tus tvs.
      refine (@lambda_exprD_ind
                          (fun tus tvs e t val'' =>
                             forall t' val val',
                               val'' = Some val ->
                               ED.lambda_exprD tus tvs t' e = Some val' ->
                               exists pf : Rty t t',
                                 Relim (exprT tus tvs) pf val' = val)
                          _ _ _ _ _ _ _ _).
      { congruence. }
      { intros; inv_all; subst.
        autorewrite with exprD_rw in *; simpl in *.
        rewrite H in *.
        destruct (type_cast t' t'0).
        { inv_all; subst. destruct r. destruct pf. exists (Rrefl _).
          reflexivity. }
        { congruence. } }
      { intros; inv_all; subst.
        autorewrite with exprD_rw in *; simpl in *.
        rewrite H in *.
        destruct (type_cast t' t'0).
        { inv_all; subst. destruct r. destruct pf. exists (Rrefl _).
          reflexivity. }
        { congruence. } }
      { intros; inv_all; subst.
        autorewrite with exprD_rw in *; simpl in *.
        unfold symAs in *.
        generalize dependent (symD i).
        rewrite pf.
        destruct pf'.
        destruct (type_cast t'0 t').
        { intros. exists (Rsym r).
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
        subst. clear - RTypeOk_typD.
        f_equal. generalize dependent (typ2 d r).
        (** NOTE(gmalecha): relying on [Rty = eq] **)
        unfold Rty. uip_all'. reflexivity.
        red in x0. uip_all'. reflexivity. }
      { intros; inv_all; subst.
        autorewrite with exprD_rw in *; simpl in *.
        forward; inv_all; subst.
        destruct (typ2_match_case t').
        { destruct H0 as [ ? [ ? [ ? ? ] ] ].
          rewrite H0 in *; clear H0.
          destruct (type_cast x d).
          { destruct r0.
            consider (ED.lambda_exprD tus (x :: tvs0) x0 e); intros.
            { eapply H in H0; clear H; eauto.
              destruct H0. destruct x2.
              subst. exists (Rsym x1). unfold exprT_Abs.
              generalize dependent (typ2_cast x r).
              destruct x1. simpl; intros.
              rewrite eq_option_eq in H1.
              inv_all; subst.
              rewrite eq_Arr_eq; rewrite eq_Const_eq. reflexivity. }
            { exfalso.
              generalize dependent (typ2_cast x x0). clear.
              destruct x1. destruct e. simpl; congruence. } }
          { exfalso.
            generalize dependent (typ2_cast x x0). clear.
            destruct x1. destruct e. simpl; congruence. } }
        { rewrite H0 in *. congruence. } }
    Qed.

    Lemma symAs_typeof_sym (f : func) (t : typ) (v : typD t) (H : symAs f t = Some v) : 
      typeof_sym f = Some t.
    Proof.
      unfold symAs in H.
      generalize dependent (symD f).
      destruct (typeof_sym f); intros; [|congruence].
      destruct (type_cast t t0) eqn:Heq; [|congruence].
      unfold type_cast in Heq.
      forward.
    Qed.

    Theorem lambda_exprD_typeof_expr
    : (*@RTypeOk _ -> Typ2Ok Typ2_Fun -> RSymOk RSym_func -> *)
      forall tus tvs e t,
        ED.typeof_expr tus tvs e = Some t <->
        exists val,
          ED.lambda_exprD tus tvs t e = Some val.
    Proof.
      intros tus tvs e; revert tvs.
      induction e; simpl; intros; autorewrite with exprD_rw; simpl.
      { split; intro.
        { consider (nth_error_get_hlist_nth typD tvs v); intros.
          { destruct s. eapply nth_error_get_hlist_nth_Some in H0.
            simpl in *. destruct H0.
            rewrite x0 in H. inv_all; subst.
            rewrite type_cast_refl; eauto. }
          { rewrite nth_error_get_hlist_nth_None in H0. congruence. } }
        { forward_reason. forward; inv_all; subst.
          destruct r. eapply nth_error_get_hlist_nth_Some in H0.
          destruct H0. assumption. } }
      { split; intros.
        { unfold symAs. generalize (symD f).
          rewrite H. rewrite type_cast_refl; eauto. }
        { forward_reason; forward.
          unfold symAs in H.
          generalize dependent (symD f).
          destruct (typeof_sym f); try congruence.
          intros. forward. } }
      { split; intros.
        { forward.
          eapply IHe1 in H. eapply IHe2 in H0.
          forward_reason.
          unfold ED.type_of_apply in H1.
          destruct (typ2_match_case t0).
          { destruct H2 as [ ? [ ? [ ? ? ] ] ].
            rewrite H2 in H1; clear H2.
            rewrite H0. generalize dependent (typ2_cast x1 x2).
            red in x3. subst.
            destruct e. simpl; intros; forward.
            destruct r. inv_all; subst. rewrite H. eauto. }
          { rewrite H2 in H1. congruence. } }
        { forward_reason; forward; inv_all; subst.
          cutrewrite (ED.typeof_expr tus tvs e1 = Some (typ2 t0 t)).
          { unfold ED.type_of_apply.
            rewrite typ2_match_iota; eauto.
            rewrite type_cast_refl; eauto.
            rewrite eq_Const_eq. reflexivity. }
          { rewrite IHe1. eauto. } } }
      { split; intros; forward; inv_all; subst.
        { rewrite typ2_match_iota; eauto.
          rewrite type_cast_refl; eauto.
          rewrite IHe in H. forward_reason.
          rewrite H. forward. eauto. }
        { forward_reason.
          destruct (typ2_match_case t0).
          { destruct H0 as [ ? [ ? [ ? ? ] ] ].
            rewrite H0 in H; clear H0.
            generalize dependent (typ2_cast x0 x1).
            red in x2. subst. simpl; intros.
            consider (type_cast x0 t); intros.
            { specialize (IHe (t :: tvs) x1).
              destruct (ED.lambda_exprD tus (t :: tvs) x1 e).
              { destruct IHe. rewrite H2; eauto. destruct r. auto. }
              { exfalso. clear - H0. destruct e0. simpl in *; congruence. } }
            { exfalso; clear - H0. destruct e0. simpl in *; congruence. } }
          { rewrite H0 in H. congruence. } } }
      { split; intro.
        { consider (nth_error_get_hlist_nth typD tus u); intros.
          { destruct s. eapply nth_error_get_hlist_nth_Some in H0.
            simpl in *. destruct H0.
            rewrite x0 in H. inv_all; subst.
            rewrite type_cast_refl; eauto. }
          { rewrite nth_error_get_hlist_nth_None in H0. congruence. } }
        { forward_reason. forward; inv_all; subst.
          destruct r. eapply nth_error_get_hlist_nth_Some in H0.
          destruct H0. assumption. } }
    Qed.

    Theorem lambda_exprD_type_cast
    : @RTypeOk typ _ -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall tus tvs e t ,
        ED.lambda_exprD tus tvs t e =
        match ED.typeof_expr (Typ2_Fun:=Typ2_Fun) tus tvs e with
          | None => None
          | Some t' =>
            match @type_cast _ _ t' t with
              | None => None
              | Some cast =>
                match ED.lambda_exprD tus tvs t' e with
                  | None => None
                  | Some x =>
                    Some (fun us gs => ED.Rcast (fun x => x) cast (x us gs))
                end
            end
        end.
    Proof.
      intros.
      consider (ED.typeof_expr tus tvs e); intros.
      { consider (type_cast t0 t); intros.
        { symmetry.
          erewrite ED.lambda_exprD_respects with (pf := Rsym r); eauto.
          clear. destruct r.
          destruct (ED.lambda_exprD tus tvs t0 e); reflexivity. }
        { consider (ED.lambda_exprD tus tvs t e); auto; intros.
          exfalso.
          rewrite lambda_exprD_typeof_expr in H1.
          destruct H1.
          destruct (lambda_exprD_single_type H1 H3).
          destruct x0. rewrite type_cast_refl in H2; eauto.
          congruence. } }
      { consider (ED.lambda_exprD tus tvs t e); auto.
        intros. exfalso.
        cut (ED.typeof_expr tus tvs e = Some t).
        congruence.
        rewrite lambda_exprD_typeof_expr. eauto. }
    Qed.

  End with_types.
End Make.
