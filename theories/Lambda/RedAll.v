Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Lambda.ExprD.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.Lambda.ExprTac.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCore.Lambda.Red.

Require Import FunctionalExtensionality.

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
          | Some vsD , Some (existT t get) =>
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
                | var_termsP_cons_None _ _ _ _ _ _ _ _ _ _ => _
                | _ => _
              end eq_refl); try solve [ destruct tvs'0 ; tauto | destruct tvs0 ; tauto ].
    intros.
    exists P'. split; auto.
    intros.
    eapply a in H0. destruct H0; clear a.
    split; auto.
    rewrite (UIP_refl pf). apply H0.
  Defined.


  Definition full_reducer : Type :=
    forall (vars : list (option (expr typ sym)))
           (e : expr typ sym)
           (args : list (expr typ sym)), expr typ sym.
  Require Import MirrorCore.SubstI.

  Fixpoint applys {ts : tenv typ} {t : typ}
           (xs : hlist typD ts) : typD (fold_right (@typ2 _ _ Fun _) t ts) -> typD t :=
    match xs in hlist _ ts return typD (fold_right (@typ2 _ _ Fun _) t ts) -> typD t with
      | Hnil => fun f => f
      | Hcons t' ts' x xs => fun f =>
        @applys ts' t xs (match typ2_cast t' (fold_right (@typ2 _ _ Fun _) t ts') in _ = t return t with
                            | eq_refl => f
                          end x)
    end.

  Definition full_reducer_ok (red : full_reducer) : Prop :=
    forall e var_terms tus tvs tus' tvs' P,
      @var_termsP tus tvs tus' tvs' var_terms P ->
      (** TODO: This is wrong, the [es] have already been converted to
       ** [tus',tvs']
       **)
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
        autorewrite with eq_rw in H7.
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
        rewrite Eq.match_eq_sym_eq'.
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
        | e => rec vars e args
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
          rewrite typ2_match_zeta in H0; eauto.
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
          autorewrite with eq_rw.
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
      Print full_reducer_ok.
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