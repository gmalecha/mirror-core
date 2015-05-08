Require Import Coq.omega.Omega.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.Util.Compat.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.Lambda.ExprTac.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCore.Lambda.Red.

Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Set Strict Implicit.

Section reducer.
  Context {sym : Type}.
  Context {typ : Type}.
  Context {RT : RType typ}
          {T2 : Typ2 _ PreFun.Fun}
          {RS : RSym sym}.

  Context {RTOk : RTypeOk}
          {T2Ok : Typ2Ok T2}
          {RSOk : RSymOk RS}.

  Context {ED_typ : EqDec _ (@eq typ)}.

  Fixpoint var_termsD tus tvs n (ls : list (option (expr typ sym)))
  : option (ExprI.exprT tus tvs Prop) :=
    match ls with
      | nil => Some (fun _ _ => True)
      | None :: ls => var_termsD tus tvs (S n) ls
      | Some l :: ls =>
        match var_termsD tus tvs (S n) ls
            , nth_error_get_hlist_nth typD tvs n
        with
          | Some vsD , Some (existT _ t get) =>
            match exprD' tus tvs t l with
              | None => None
              | Some vD => Some (fun us vs => get vs = vD us vs /\ vsD us vs)
            end
          | None , _ => None
          | _ , None => None
        end
    end.

  Theorem var_termsD_sem tus tvs
  : forall ls n P,
      var_termsD tus tvs n ls = Some P ->
      (forall u e,
         nth_error ls u = Some (Some e) ->
         exists t get (vD : ExprI.exprT tus tvs (typD t)),
           nth_error_get_hlist_nth typD tvs (n + u) = Some (@existT _ _ t get) /\
           exprD' tus tvs t e = Some vD /\
           forall us vs,
             P us vs -> get vs = vD us vs).
  Proof.
    induction ls; simpl; intros; inv_all.
    - subst. exfalso.
      destruct u; simpl in *; inversion H0.
    - destruct u.
      + simpl in *. inversion H0; clear H0; subst.
        forward. inv_all; subst.
        cutrewrite (n + 0 = n); [ | omega ].
        do 3 eexists; split; eauto; split; eauto.
        intros. tauto.
      + simpl in H0.
        cutrewrite (n + S u = (S n) + u); [ | omega ].
        destruct a; eauto.
        forward; inv_all; subst.
        specialize (IHls _ _ H _ _ H0).
        forward_reason.
        do 3 eexists; split; eauto. split; eauto.
        firstorder.
  Qed.

  (** I want this to capture the fact that when the entry is [Some], then
   ** the "resulting environment" does not contain the entry.
   ** 1) State a relation between the pre- and post-environments
   **    (i.e. the hlists)
   **)
  Inductive var_termsP
  : forall (tus tvs tus' tvs' : tenv typ),
      list (option (expr typ sym)) ->
      ExprI.exprT tus tvs (ExprI.exprT tus' tvs' Prop) ->
      Prop :=
  | var_termsP_nil
    : forall tus tvs (P : ExprI.exprT tus tvs (ExprI.exprT tus tvs Prop)),
        (forall us vs us' vs', P us vs us' vs' -> us = us' /\ vs = vs') ->
        @var_termsP tus tvs tus tvs nil P
  | var_termsP_cons_None
    : forall t tus tvs tus' tvs' p
             (P : ExprI.exprT tus (t :: tvs) (ExprI.exprT tus' (t :: tvs') Prop))
             (P' : ExprI.exprT tus tvs (ExprI.exprT tus' tvs' Prop)),
        @var_termsP tus tvs tus' tvs' p P' ->
        (forall us (vs : HList.hlist typD (t :: tvs))
                us' (vs' : HList.hlist typD (t :: tvs')),
           P us vs us' vs' ->
           hlist_hd vs = hlist_hd vs' /\
           P' us (hlist_tl vs) us' (hlist_tl vs')) ->
        @var_termsP tus (t :: tvs) tus' (t :: tvs') (None :: p) P
  | var_termsP_cons_Some
    : forall t tus tvs tus' tvs' p e eD
             (P : ExprI.exprT tus (t :: tvs) (ExprI.exprT tus' tvs' Prop))
             (P' : ExprI.exprT tus tvs (ExprI.exprT tus' tvs' Prop)),
        @var_termsP tus tvs tus' tvs' p P' ->
        exprD' tus' tvs' t e = Some eD ->
        (forall us (vs : HList.hlist typD (t :: tvs))
                us' (vs' : HList.hlist typD tvs'),
           P us vs us' vs' ->
           P' us (hlist_tl vs) us' vs' /\
           hlist_hd vs = eD us' vs') ->
        @var_termsP tus (t :: tvs) tus' tvs' (Some e :: p) P.

  Instance Injective_var_termsP t var_terms tus tvs tus' tvs' P
  : Injective (@var_termsP tus (t :: tvs) tus' (t :: tvs')
                           (@None (expr typ sym) :: var_terms)
                           P) :=
    {| result := exists P',
                   @var_termsP tus tvs tus' tvs' var_terms P' /\
                   (forall us (vs : HList.hlist typD (t :: tvs))
                           us' (vs' : HList.hlist typD (t :: tvs')),
                      P us vs us' vs' ->
                      hlist_hd vs = hlist_hd vs' /\
                      P' us (hlist_tl vs) us' (hlist_tl vs')) |}.
  Proof.
    refine (fun H =>
              match H in @var_termsP a b c d X P
                    return match b as b , d as d , X
                                 return ExprI.exprT a b (ExprI.exprT c d Prop) -> Prop
                           with
                             | t :: b , t' :: d , None :: var_terms =>
                               fun P => forall pf : t = t' ,
                                        exists P',
                                          @var_termsP a b c d var_terms P' /\
                                          (forall (us : HList.hlist typD a) (vs : HList.hlist typD (t :: b))
                                                  (us' : HList.hlist typD c) (vs' : HList.hlist typD (t' :: d)),
                                             P us vs us' vs' ->
                                             hlist_hd vs = match eq_sym pf in _ = t return typD t with
                                                             | eq_refl => hlist_hd vs'
                                                           end /\
                                             P' us (hlist_tl vs) us' (hlist_tl vs')) 
                             | _ , _ , _ => fun _ => True
                           end P
              with
                | var_termsP_cons_None _ _ _ => _
                | _ => _
              end eq_refl); try solve [ destruct t1 ; tauto | destruct t2 ; tauto ].
    intros.
    exists e0. split; auto.
    intros.
    eapply a in H0. destruct H0; clear a.
    split; auto.
    rewrite (UIP_refl pf). apply H0.
    destruct t3; exact I.
  Defined.


  Definition full_reducer : Type :=
    forall (vars : list (option (expr typ sym)))
           (e : expr typ sym)
           (args : list (expr typ sym)), expr typ sym.

  Fixpoint applys {ts : tenv typ} {t : typ}
           (xs : hlist typD ts) : typD (fold_right (@typ2 _ _ Fun _) t ts) -> typD t :=
    match xs in hlist _ ts return typD (fold_right (@typ2 _ _ Fun _) t ts) -> typD t with
      | Hnil => fun f => f
      | @Hcons _ _ t' ts' x xs => fun f =>
        @applys ts' t xs (match typ2_cast t' (fold_right (@typ2 _ _ Fun _) t ts') in _ = t return t with
                            | eq_refl => f
                          end x)
    end.

  Definition full_reducer_ok (red : full_reducer) : Prop :=
    forall e var_terms tus tvs tus' tvs' P,
      @var_termsP tus tvs tus' tvs' var_terms P ->
      forall es t targs fD esD,
      let arrow_type := fold_right (@typ2 _ _ Fun _) t targs in
      exprD' tus tvs arrow_type e = Some fD ->
      hlist_build (fun t => ExprI.exprT tus' tvs' (typD t))
                  (fun t e => exprD' tus' tvs' t e) targs es = Some esD ->
      exists val',
        exprD' tus' tvs' t (red var_terms e es) = Some val' /\
        forall us vs us' vs',
          P us vs us' vs' ->
          applys
            (hlist_map (fun t (x : ExprI.exprT tus' tvs' (typD t)) => x us' vs') esD)
            (fD us vs) = val' us' vs'.

  Definition partial_reducer : Type :=
    forall (e : expr typ sym)
           (args : list (expr typ sym)), expr typ sym.
  (** TODO: This pattern seems common enough to warrent something
   ** interesting
   **)
  Definition partial_reducer_ok (red : partial_reducer) : Prop :=
    forall e es t tus tvs val P,
      exprD' tus tvs t (apps e es) = Some val ->
      exists val',
        exprD' tus tvs t (red e es) = Some val' /\
        forall us vs,
          P us vs ->
          val us vs = val' us vs.

  Definition apps_reducer : partial_reducer :=
    @apps typ sym.

  Theorem apps_partial_reducer_ok : partial_reducer_ok apps_reducer.
  Proof.
    unfold apps_reducer; red. intros. eauto.
  Qed.

  (** [acc] is the amount to lift by
   ** this is because there is some fancyness going on since applied lambdas
   ** actually remove entries from the environment
   **)
  Fixpoint get_var (v : nat) (ls : list (option (expr typ sym)))
           (acc : nat) {struct ls}
  : expr typ sym :=
    match ls with
      | nil => Var (acc + v)
      | None :: ls =>
        match v with
          | 0 => Var acc
          | S v => get_var v ls (S acc)
        end
      | Some e :: ls =>
        match v with
          | 0 => lift 0 acc e
          | S v => get_var v ls acc
        end
    end.

  Let exprD'_conv :=
    @ExprI.exprD'_conv typ RT (expr typ sym) (@Expr_expr typ sym RT _ _).

  Lemma get_var_type_ok
  : forall tus tvs tus'  tvs' var_terms P,
      @var_termsP tus tvs tus' tvs' var_terms P ->
      forall _tvs _tvs' v t,
      let acc := length _tvs' in
        typeof_expr tus  (_tvs ++ tvs) (Var (length _tvs + v)) = Some t ->
        typeof_expr tus' (_tvs' ++ tvs') (get_var v var_terms acc) = Some t.
  Proof.
    induction 1; simpl; intros; auto.
    { rewrite ListNth.nth_error_app_R in H0 by omega.
      rewrite ListNth.nth_error_app_R by omega.
      cutrewrite (length _tvs + v - length _tvs = v) in H0; [ | omega ].
      cutrewrite (length _tvs' + v - length _tvs' = v); [ | omega ].
      assumption. }
    { destruct v.
      { simpl.
        rewrite ListNth.nth_error_app_R in H1 by omega.
        rewrite ListNth.nth_error_app_R by omega.
        revert H1.
        rewrite Plus.plus_0_r.
        do 2 rewrite Minus.minus_diag. exact (fun x => x). }
      { replace (length _tvs + S v)
           with (length (_tvs ++ t :: nil) + v) in H1
             by (rewrite app_length; simpl; omega).
        replace (S (length _tvs'))
           with (length (_tvs' ++ t :: nil))
             by (rewrite app_length; simpl; omega).
        replace (_tvs' ++ t :: tvs')
           with ((_tvs' ++ t :: nil) ++ tvs')
             by (rewrite app_ass; reflexivity).
        replace (_tvs ++ t :: tvs)
           with ((_tvs ++ t :: nil) ++ tvs) in H1
             by (rewrite app_ass; reflexivity).
        eapply IHvar_termsP; eauto. } }
    { destruct v.
      { eapply exprD_typeof_Some in H0; eauto.
        rewrite ListNth.nth_error_app_R in H2 by omega; eauto.
        cutrewrite (length _tvs + 0 - length _tvs = 0) in H2; [ | omega ].
        simpl in H2. inversion H2; clear H2; subst.
        change 0 with (length (@nil typ)).
        change (_tvs' ++ tvs') with (nil ++ _tvs' ++ tvs').
        rewrite typeof_expr_lift. assumption. }
      { replace (length _tvs + S v)
           with (length (_tvs ++ t :: nil) + v) in H2
             by (rewrite app_length; simpl; omega).
        replace (_tvs ++ t :: tvs)
           with ((_tvs ++ t :: nil) ++ tvs) in H2
             by (rewrite app_ass; reflexivity).
        eapply IHvar_termsP; eauto. } }
  Qed.

  Lemma nth_error_get_hlist_nth_rwR
  : forall {T} (F : T -> _) tus tvs' n,
      n >= length tus ->
      match nth_error_get_hlist_nth F tvs' (n - length tus) with
        | None => True
        | Some (existT _ t v) =>
          exists val,
          nth_error_get_hlist_nth F (tus ++ tvs') n = Some (@existT _ _ t val) /\
          forall a b,
            v a = val (hlist_app b a)
      end.
  Proof.
    clear. intros.
    forward. subst.
    consider (nth_error_get_hlist_nth F (tus ++ tvs') n).
    { intros.
      eapply nth_error_get_hlist_nth_appR in H; eauto.
      destruct s. simpl in *. rewrite H1 in *.
      destruct H as [ ? [ ? ? ] ]. inv_all; subst.
      eexists; split; eauto. }
    { intros.
      exfalso.
      eapply nth_error_get_hlist_nth_Some in H1.
      eapply nth_error_get_hlist_nth_None in H0.
      forward_reason. simpl in *.
      eapply ListNth.nth_error_length_ge in H0.
      clear H1. eapply nth_error_length_lt in x0.
      rewrite app_length in H0. omega. }
  Qed.


  Lemma get_var_ok
  : forall tus tvs tus'  tvs' var_terms P,
      @var_termsP tus tvs tus' tvs' var_terms P ->
      forall _tvs _tvs' v t val,
      let acc := length _tvs' in
        exprD' tus (_tvs ++ tvs) t (Var (length _tvs + v)) = Some val ->
        exists val',
          exprD' tus' (_tvs' ++ tvs') t (get_var v var_terms acc) = Some val' /\
          forall us _vs vs us' _vs' vs',
            P us vs us' vs' ->
            val us (hlist_app _vs vs) =
            val' us' (hlist_app _vs' vs').
  Proof.
    induction 1; simpl; intros.
    { revert H0.
      autorewrite with exprD_rw. simpl.
      intros; forward; inv_all; subst.
      eapply nth_error_get_hlist_nth_appR in H1; [ | omega ]. simpl in H1.
      replace (length _tvs + v - length _tvs) with v in H1 by omega.
      forward_reason.
      assert (length _tvs' + v >= length _tvs') by omega.
      generalize (@nth_error_get_hlist_nth_rwR typ typD _tvs' tvs _ H3).
      replace (length _tvs' + v - length _tvs') with v by omega.
      rewrite H0.
      intros; forward_reason; Cases.rewrite_all_goal.
      eexists; split; eauto.
      simpl. intros. f_equal. etransitivity. eapply H1.
      apply H in H6. destruct H6; subst. eauto. }
    { destruct v.
      { rewrite Plus.plus_0_r in *.
        revert H1. autorewrite with exprD_rw. simpl.
        clear IHvar_termsP.
        intros; forward; inv_all; subst.
        assert (length _tvs' >= length _tvs') by omega.
        generalize (@nth_error_get_hlist_nth_rwR typ typD _tvs' (t :: tvs') _ H1).
        rewrite Minus.minus_diag. simpl.
        intros; forward_reason.
        Cases.rewrite_all_goal.
        eapply nth_error_get_hlist_nth_appR in H2; [ | omega ]. simpl in *.
        rewrite Minus.minus_diag in H2. simpl.
        forward_reason; inv_all; subst.
        rewrite H3.
        eexists; split; eauto.
        simpl; intros. f_equal.
        rewrite H6; clear H6.
        subst. apply H0 in H2; clear H0.
        destruct H2. etransitivity; eauto. }
      { revert H1.
        specialize (IHvar_termsP (_tvs ++ t :: nil) (_tvs' ++ t :: nil) v t0).
        revert IHvar_termsP.
        autorewrite with exprD_rw.
        simpl. intros.
        forward. inv_all; subst.
        eapply nth_error_get_hlist_nth_appR in H2; [ | omega ].
        simpl in *.
        replace (length _tvs + S v - length _tvs) with (S v) in H2; [ | omega ].
        forward_reason.
        forward; inv_all; subst.
        assert (length (_tvs ++ t :: nil) + v >= length (_tvs ++ t :: nil)) by omega.
        subst.
        generalize (@nth_error_get_hlist_nth_rwR _ typD (_tvs ++ t :: nil) tvs (length (_tvs ++ t :: nil) + v) H1).
        replace (length (_tvs ++ t :: nil) + v - length (_tvs ++ t :: nil)) with v by omega.
        rewrite H4. intros; forward_reason.
        revert IHvar_termsP.
        rewrite H5. rewrite H3. intro IH.
        specialize (IH _ eq_refl).
        forward_reason.
        rewrite app_length in H7. simpl in H7.
        rewrite Plus.plus_comm in H7. simpl in H7.
        rewrite exprD'_conv
           with (pfu := eq_refl) (pfv := eq_sym (app_ass_trans _ _ _)) in H7.

        autorewrite_with_eq_rw_in H7.
        forward; inv_all; subst.
        simpl in *. eexists; split; eauto.
        intros.
        eapply H0 in H9; clear H0.
        destruct H9.
        rewrite H2; clear H2.
        specialize (H8 us (hlist_app _vs (fst (hlist_split (t :: nil) tvs vs)))
                       (snd (hlist_split (t :: nil) tvs vs)) us'
                       (hlist_app _vs' (fst (hlist_split (t :: nil) tvs' vs')))
                       (snd (hlist_split (t :: nil) tvs' vs'))).
        eapply H8 in H9; clear H8; simpl in *.
        rewrite <- H6 in H9; clear H6.
        rewrite H9; clear H9.
        autorewrite with eq_rw.
        f_equal. rewrite hlist_app_assoc.
        clear.
        rewrite Eq.match_eq_sym_eq.
        f_equal.
        symmetry. apply (hlist_eta vs'). } }
    { destruct v.
      { clear IHvar_termsP.
        generalize (@exprD'_lift typ sym _ _ _ _ _ _ tus' e nil _tvs' tvs' t).
        simpl. rewrite H0. intros; forward.
        assert (t = t0).
        { revert H2.
          autorewrite with exprD_rw. clear.
          simpl; intros; forward.
          clear H2. subst.
          eapply nth_error_get_hlist_nth_appR in H0; [ | omega ].
          simpl in H0.
          replace (length _tvs + 0 - length _tvs) with 0 in H0 by omega.
          forward_reason.
          inv_all. subst. apply r. }
        subst.
        eexists; split; eauto.
        intros. specialize (H4 us' Hnil _vs' vs').
        simpl in H4.
        autorewrite with exprD_rw in H2.
        simpl in H2.
        forward; inv_all; subst.
        eapply H1 in H5; clear H1.
        rewrite <- H4; clear H4.
        destruct H5. rewrite <- H2; clear H2.
        eapply nth_error_get_hlist_nth_appR in H6; [ | omega ].
        simpl in *.
        replace (length _tvs + 0 - length _tvs) with 0 in H6 by omega.
        forward_reason; inv_all; subst.
        rewrite H4; clear H4.
        subst.
        red in r.
        rewrite (UIP_refl r). reflexivity. }
      { revert H2.
        specialize (IHvar_termsP (_tvs ++ t :: nil) _tvs' v t0).
        revert IHvar_termsP.
        autorewrite with exprD_rw.
        simpl. intros.
        forward. inv_all; subst.
        eapply nth_error_get_hlist_nth_appR in H3; [ | omega ].
        simpl in *.
        replace (length _tvs + S v - length _tvs) with (S v) in H3; [ | omega ].
        forward_reason.
        forward; inv_all; subst.
        assert (length (_tvs ++ t :: nil) + v >= length (_tvs ++ t :: nil)) by omega.
        subst.
        generalize (@nth_error_get_hlist_nth_rwR _ typD (_tvs ++ t :: nil) tvs (length (_tvs ++ t :: nil) + v) H2).
        replace (length (_tvs ++ t :: nil) + v - length (_tvs ++ t :: nil)) with v by omega.
        rewrite H5. intros; forward_reason.
        revert IHvar_termsP.
        rewrite H6. rewrite H4. intro IH.
        specialize (IH _ eq_refl).
        forward_reason.
        forward; inv_all; subst.
        simpl in *. eexists; split; eauto.
        intros.
        eapply H1 in H10; clear H1.
        destruct H10.
        specialize (H9 us (hlist_app _vs (fst (hlist_split (t :: nil) tvs vs)))
                       (snd (hlist_split (t :: nil) tvs vs)) us' _vs' vs').
        simpl in H9. eapply H9 in H1; clear H9.
        rewrite H3; clear H3.
        erewrite H7; clear H7.
        eapply H1. } }
  Qed.

  Section id.
    Fixpoint idred' (vars : list (option (expr typ sym)))
               (e : expr typ sym) : expr typ sym :=
      match e with
        | Inj i => Inj i
        | UVar u => UVar u
        | Var v => get_var v vars 0
        | App e1 e2 => App (idred' vars e1) (idred' vars e2)
        | Abs t e => Abs t (idred' (None :: vars) e)
      end.

    Variable par_red : partial_reducer.
    Hypothesis par_redOk : partial_reducer_ok par_red.

    Definition idred (vars : list (option (expr typ sym)))
               (e : expr typ sym)
               (args : list (expr typ sym)) : expr typ sym :=
      par_red (idred' vars e) args.

    Lemma idred'_type_ok
    : forall e var_terms tus tvs tus' tvs' P,
        @var_termsP tus tvs tus' tvs' var_terms P ->
        forall t,
          typeof_expr tus tvs e = Some t ->
          typeof_expr tus' tvs' (idred' var_terms e) = Some t.
    Proof.
      induction e; simpl; intros; eauto.
      { eapply get_var_type_ok with (_tvs' := nil) (_tvs := nil); eauto. }
      { forward.
        erewrite IHe1 by eauto.
        erewrite IHe2 by eauto. eauto. }
      { forward. inv_all; subst.
        erewrite IHe; eauto.
        econstructor. eassumption.
        instantiate (1 := fun us vs us' vs' =>
                            hlist_hd vs = hlist_hd vs' /\
                            P us (hlist_tl vs) us' (hlist_tl vs')).
        auto. }
      { revert H0. clear - H.
        (** This is because [var_termsP] also mentions unification
         ** variables when it actually does not need to
         **)
        induction H; simpl; intros; eauto. }
    Qed.

    Lemma var_termsP_tus_same
    : forall tus tvs tus' tvs' vts P,
        @var_termsP tus tvs tus' tvs' vts P ->
        tus = tus'.
    Proof.
      clear. induction 1; auto.
    Qed.

    Lemma idred'_ok
    : forall e var_terms tus tvs tus' tvs' P,
        @var_termsP tus tvs tus' tvs' var_terms P ->
        forall t fD,
          exprD' tus tvs t e = Some fD ->
          exists val',
            exprD' tus' tvs' t (idred' var_terms e) = Some val' /\
            forall us vs us' vs',
              P us vs us' vs' ->
              fD us vs = val' us' vs'.
    Proof.
      induction e; simpl; intros.
      { change v with (0 + v) in H0.
        change tvs with (nil ++ tvs) in H0.
        eapply get_var_ok in H0; eauto.
        revert H0. instantiate (1 := nil). simpl.
        intros. forward_reason. eexists; split; eauto.
        intros. apply (H1 us Hnil vs us' Hnil vs' H2). }
      { revert H0.
        autorewrite with exprD_rw. simpl.
        intros; forward; inv_all; subst.
        eexists; split; eauto. }
      { revert H0. autorewrite with exprD_rw; simpl.
        forward; inv_all; subst.
        specialize (@IHe1 var_terms tus tvs tus' tvs' P H (typ2 t0 t) _ H1).
        specialize (@IHe2 var_terms tus tvs tus' tvs' P H t0 _ H2).
        forward_reason.
        erewrite idred'_type_ok; eauto.
        Cases.rewrite_all_goal.
        eexists; split; eauto.
        intros.
        specialize (H6 _ _ _ _ H7).
        specialize (H5 _ _ _ _ H7).
        unfold exprT_App.
        autorewrite_with_eq_rw.
        destruct H6; destruct H5; reflexivity. }
      { revert H0.
        autorewrite with exprD_rw; simpl; intros.
        arrow_case_any; try congruence.
        clear H1.
        red in x1; subst.
        simpl in *.
        revert H0.
        autorewrite with eq_rw.
        intros; forward; inv_all; subst.
        eapply IHe with (P:=fun us vs us' vs' =>
                            hlist_hd vs = hlist_hd vs' /\
                            P us (hlist_tl vs) us' (hlist_tl vs')) in H2.
        - destruct H2 as [ ? [ ? ? ] ].
          rewrite H1. eexists; split; eauto.
          intros.
          autorewrite with eq_rw.
          destruct (eq_sym (typ2_cast x x0)).
          eapply functional_extensionality; intro.
          eapply H2; eauto.
        - econstructor; eauto. }
      { revert H0. autorewrite with exprD_rw. simpl.
        intros; forward; inv_all; subst.
        revert H1. destruct r.
        induction H.
        { intro. rewrite H1. rewrite H2.
          eexists; split; eauto. simpl.
          intros. eapply H in H0. destruct H0; subst.
          reflexivity. }
        { intro. eapply IHvar_termsP in H1.
          forward_reason. forward.
          inv_all; subst.
          eexists; split; eauto.
          intros. eapply H0 in H1.
          destruct H1. eapply H3 in H6. auto. }
        { intro. eapply IHvar_termsP in H3.
          forward_reason. forward.
          inv_all; subst.
          eexists; split; eauto.
          intros. eapply H1 in H3.
          destruct H3. eapply H4 in H3. auto. } }
    Qed.

    Lemma idred_ok : full_reducer_ok idred.
    Proof.
      unfold idred. red.
      intros.
      eapply idred'_ok in H0; eauto.
      forward_reason.
      assert (exists xD,
                exprD' tus' tvs' t (apps (idred' var_terms e) es) = Some xD /\
                forall us' vs',
                  xD us' vs' =
                  applys
                    (hlist_map (fun t (x : ExprI.exprT tus' tvs' (typD t)) =>
                                  x us' vs') esD) (x us' vs')).
      { rewrite exprD'_apps by eauto.
        unfold apps_sem'.
        erewrite exprD_typeof_Some by eauto.
        rewrite H0. clear H2.
        clear H0. revert H1. revert esD.
        revert x. clear fD. revert es.
        induction targs; destruct es; try solve [ inversion 1 ]; simpl; intros.
        { inversion H1; subst.
          rewrite type_cast_refl; eauto. }
        { rewrite typ2_match_iota; eauto.
          forward; inv_all; subst.
          eapply IHtargs in H0; eauto.
          forward_reason.
          autorewrite_with_eq_rw.
          erewrite H0.
          eexists; split; [ reflexivity | ].
          simpl in *. intros.
          autorewrite_with_eq_rw. eauto. } }
      { forward_reason.
        eapply par_redOk in H3; eauto.
        forward_reason.
        eexists; split; eauto.
        intros. erewrite H2 by eauto; clear H2.
        rewrite <- H5; eauto.
        instantiate (1 := fun _ _ => True). exact I. }
    Qed.

  End id.

  Section delta_list.
    Variable orelse : full_reducer.
    Variable delta : sym -> option (expr typ sym).

    Definition delta_all (vars : list (option (expr typ sym)))
               (e : expr typ sym)
               (args : list (expr typ sym)) : expr typ sym :=
      match e with
        | Inj i => match delta i with
                     | None => apps (Inj i) args
                     | Some e => orelse vars e args
                   end
        | e => orelse vars e args
      end.

    Hypothesis orelse_ok : full_reducer_ok orelse.
    Hypothesis delta_ok
    : forall i e,
        delta i = Some e ->
        forall t eD,
          exprD' nil nil t (Inj i) = Some eD ->
          exists eD',
            exprD' nil nil t e = Some eD' /\
            eD Hnil Hnil = eD' Hnil Hnil.
    Theorem delta_all_ok : full_reducer_ok delta_all.
    Proof.
      red. destruct e; eauto.
      specialize (@delta_ok s).
      simpl.
      destruct (delta s).
      - intros.
        specialize (@delta_ok _ eq_refl (fold_right (typ2 (F:=Fun)) t targs)).
        revert delta_ok. revert H0.
        autorewrite with exprD_rw; simpl; intros.
        forward.
        specialize (@delta_ok _ eq_refl).
        destruct delta_ok. destruct H3. subst.
        clear delta_ok.
        inv_all; subst. clear H0.
        eapply ExprFacts.exprD'_weaken in H3; eauto.
        revert H3. instantiate (1 := tvs). instantiate (1 := tus).
        simpl. intros.
        forward_reason.
        eapply orelse_ok in H0; eauto.
        eapply H0 in H1; clear H0.
        forward_reason; eexists; split; eauto.
        intros. erewrite <- H1; eauto.
        f_equal.
        specialize (H2 Hnil Hnil us vs). assumption.
      - intros.
        rewrite exprD'_apps; eauto.
        unfold apps_sem'.
        cutrewrite (typeof_expr tus' tvs' (Inj s) =
                    Some (fold_right (typ2 (F:=Fun)) t targs)).
        + revert H0.
          autorewrite with exprD_rw. simpl.
          intro; forward; inv_all; subst.
          change
            (exists val' : ExprI.exprT tus' tvs' (typD t),
               apply_sem' T2 RS (fold_right (typ2 (F:=Fun)) t targs)
                          (fun (us : hlist typD tus') (vs : hlist typD tvs') =>
                             (fun (_ : hlist typD tus') (_ : hlist typD tvs') => t0) us vs) es t =
               Some val' /\
               (forall (us : hlist typD tus) (vs : hlist typD tvs)
                       (us' : hlist typD tus') (vs' : hlist typD tvs'),
                  P us vs us' vs' ->
                  applys
                    (hlist_map
                       (fun (t1 : typ) (x : ExprI.exprT tus' tvs' (typD t1)) => x us' vs')
                       esD) ((fun (_ : hlist typD tus') (_ : hlist typD tvs') => t0) us' vs') = val' us' vs')).
          generalize (fun (_ : hlist typD tus') (_ : hlist typD tvs') => t0).
          revert H1. clear H0 H t0.
          revert es.
          induction targs; destruct es; simpl in *; try congruence;
          intros; inv_all; subst.
          * rewrite type_cast_refl; eauto.
          * rewrite typ2_match_iota; simpl; eauto.
            forward; inv_all; subst.
            autorewrite_with_eq_rw.
            simpl.
            eapply IHtargs in H; eauto.
            forward_reason.
            rewrite H. eexists; split; eauto.
            autorewrite_with_eq_rw.
            eauto.
        + eapply exprD_typeof_Some in H0; eauto.
    Qed.
  End delta_list.

  Section beta_all.
    Variable rec : full_reducer.

    Fixpoint beta_all_gen
             (vars : list (option (expr typ sym)))
             (e : expr typ sym)
             (args : list (expr typ sym)) : expr typ sym :=
      match e with
        | App e' e'' =>
          beta_all_gen vars e' (beta_all_gen vars e'' nil :: args)
        | Abs t e' =>
          match args with
            | nil => Abs t (beta_all_gen (None :: vars) e' nil) (** args = nil **)
            | a :: args => beta_all_gen (Some a :: vars) e' args
          end
        | Var v =>
          (** [get_var] has already done the conversion! **)
          rec nil (get_var v vars 0) args
        | UVar u => rec vars (UVar u) args
        | Inj i => rec vars (Inj i) args
      end.

    Hypothesis rec_sound : full_reducer_ok rec.

    Theorem beta_all_gen_sound : full_reducer_ok beta_all_gen.
    Proof.
      red. induction e; try solve [ simpl; intros; eauto ].
      { (* Var *)
        simpl; intros.
        generalize (@get_var_ok _ _ _ _ _ _ H nil nil v _ _ H0).
        clear H0; intros.
        forward_reason. simpl in *.
        eapply rec_sound in H0; eauto.
        Focus 2. eapply var_termsP_nil.
        intros. eapply H3.
        eapply H0 in H1; clear H0.
        forward_reason.
        eexists; split; eauto. intros.
        eapply H2 with (_vs := Hnil) (_vs' := Hnil) in H3.
        specialize (H1 us' vs' us' vs' (conj eq_refl eq_refl)).
        simpl in *. rewrite H3. eapply H1. }
      { (* App *)
        simpl; intros.
        autorewrite with exprD_rw in H0. simpl in H0.
        forward; inv_all; subst.
        specialize (IHe2 var_terms tus tvs tus' tvs' _ H nil t0 nil _ _ H3 eq_refl).
        forward_reason.
        specialize (@IHe1 var_terms _ _ _ _ _ H (beta_all_gen var_terms e2 nil :: es) _ (t0 :: targs) _
                          (@Hcons _ _ t0 _ x esD) H2).
        simpl in IHe1.
        rewrite H1 in IHe1.
        rewrite H4 in IHe1. specialize (IHe1 eq_refl).
        forward_reason.
        eexists; split; eauto.
        intros.
        specialize (H5 _ _ _ _ H8).
        specialize (H7 _ _ _ _ H8).
        rewrite <- H5 in H7; clear H5. simpl in H7.
        unfold exprT_App.
        match goal with
          | H : context [ match ?X with _ => _ end ]
            |- context [ match eq_sym ?Y with _ => _ end ] =>
            change Y with X; generalize dependent X
        end.
        clear.
        generalize dependent (typD (typ2 t0 (fold_right (typ2 (F:=Fun)) t targs))).
        intros; subst. simpl in *. eauto. }
      { (* Abs *)
        simpl; intros.
        destruct es.
        { destruct targs; simpl in *; try congruence.
          inv_all; subst.
          revert H0.
          autorewrite with exprD_rw; simpl.
          intros.
          arrow_case_any; try congruence.
          red in x1. subst. simpl in *.
          revert H0.
          autorewrite with eq_rw. intros; forward; inv_all; subst.
          assert (@var_termsP tus (t :: tvs) tus' (t :: tvs')
                              (None :: var_terms)
                              (fun us vs us' vs' =>
                                 P us (hlist_tl vs) us' (hlist_tl vs') /\
                                 hlist_hd vs = hlist_hd vs')).
          { eapply var_termsP_cons_None. eassumption.
            clear. tauto. }
          specialize (@IHe _ _ _ _ _ _ H2 nil x0 nil _ _ H3 eq_refl).
          simpl in IHe.
          forward_reason.
          rewrite H4.
          eexists; split; eauto.
          intros.
          autorewrite with eq_rw.
          inv_all.
          clear H1.
          apply Data.Eq.match_eq_match_eq with (F := fun x => x).
          apply functional_extensionality. intros.
          eapply H5. simpl.
          split; auto. }
        { destruct targs; simpl in *; try congruence.
          forward; inv_all; subst.
          autorewrite with exprD_rw in H0.
          rewrite typ2_match_iota in H0; eauto.
          simpl in H0.
          autorewrite with eq_rw in H0.
          forward; inv_all; subst.
          destruct r. rename t1 into t.
          assert (@var_termsP tus (t :: tvs) tus' tvs'
                              (Some e0 :: var_terms)
                              (fun us vs us' vs' =>
                                 P us (hlist_tl vs) us' vs' /\
                                 hlist_hd vs = e1 us' vs' )).
          { econstructor; eauto. }
          specialize (IHe (Some e0 :: var_terms) _ _ _ _ _ H3 es t0 targs _ _ H4 H1).
          forward_reason.
          eexists; split; eauto.
          intros.
          simpl.
          specialize (H6 us (Hcons (e1 us' vs') vs) us' vs' (conj H7 eq_refl)).
          autorewrite_with_eq_rw.
          rewrite Data.Eq.match_eq_sym_eq with (F:=fun x=>x).
          eauto. } }
    Qed.

    Definition beta_all e := beta_all_gen nil e nil.

    Theorem beta_all_sound
    : forall e t tus tvs val P,
      exprD' tus tvs t e = Some val ->
      exists val',
        exprD' tus tvs t (beta_all e) = Some val' /\
        forall us vs,
          P us vs ->
          val us vs = val' us vs.
    Proof.
      intros.
      assert (var_termsP nil
                         (fun (us : hlist typD tus) (vs : hlist typD tvs)
                              (us' : hlist typD tus) (vs' : hlist typD tvs) =>
                            us = us' /\ vs = vs')).
      { constructor. tauto. }
      specialize (@beta_all_gen_sound e nil _ _ _ _ _ H0 nil t nil _ _ H eq_refl).
      simpl.
      intros. forward_reason.
      eauto.
    Qed.

  End beta_all.

  Section interleave.
    Variables f g : full_reducer -> full_reducer.

    Fixpoint interleave (n : nat) : full_reducer :=
      match n with
        | 0 => idred (@apps _ _)
        | S n => fun x => f (fun x => g (fun x => interleave n x) x) x
      end.


    Hypothesis f_ok : forall x, full_reducer_ok x -> full_reducer_ok (f x).
    Hypothesis g_ok : forall x, full_reducer_ok x -> full_reducer_ok (g x).

    Theorem interleave_ok : forall n, full_reducer_ok (interleave n).
    Proof.
      induction n; simpl; intros.
      - eapply idred_ok. eapply apps_partial_reducer_ok.
      - eapply f_ok. eapply g_ok. eapply IHn.
    Qed.
  End interleave.

End reducer.

(*
Section test.
  Context {sym : Type}.
  Context {typ : Type}.
  Context {RT : RType typ}
          {T2 : Typ2 _ PreFun.Fun}
          {RS : RSym sym}.

  Context {RTOk : RTypeOk}
          {T2Ok : Typ2Ok T2}
          {RSOk : RSymOk RS}.

  Context {ED_typ : EqDec _ (@eq typ)}.

  Eval compute in fun t =>
                    beta_all (@apps typ sym) nil nil (App (Abs t (App (Var 10) (Abs t (Var 1)))) (Var 0)).
*)