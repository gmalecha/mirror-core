Require Import Coq.omega.Omega.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Lambda.ExprD.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.Util.Compat.

Require Import FunctionalExtensionality.

Set Implicit Arguments.
Set Strict Implicit.

Section substitute.
  Context {typ : Set}.
  Context {sym : Set}.
  Context {RT : RType typ}
          {T2 : Typ2 _ RFun}
          {RS : RSym sym}.

  Context {RTOk : RTypeOk}
          {T2Ok : Typ2Ok T2}
          {RSOk : RSymOk RS}.

  Context {ED_typ : EqDec _ (@eq typ)}.

  Fixpoint substitute_one (v : var) (w : expr typ sym) (e : expr typ sym)
  : expr typ sym :=
    match e with
    | Var v' =>
      match nat_compare v v' with
      | Eq => w
      | Lt => Var (v' - 1)
      | Gt => Var v'
      end
    | UVar u => UVar u
    | Inj i => Inj i
    | App l' r' => App (substitute_one v w l') (substitute_one v w r')
    | Abs t e => Abs t (substitute_one (S v) (lift 0 1 w) e)
    end.

  Theorem substitute_one_typed
  : forall tus t e w tvs' tvs t',
      typeof_expr tus (tvs ++ tvs') w = Some t ->
      typeof_expr tus (tvs ++ t :: tvs') e = Some t' ->
      typeof_expr tus (tvs ++ tvs') (substitute_one (length tvs) w e) = Some t'.
  Proof.
    induction e; simpl; intros;
    forward; inv_all; subst; Cases.rewrite_all_goal; auto.
    { consider (nat_compare (length tvs) v).
      { intros. apply nat_compare_eq in H1.
        subst. rewrite nth_error_app_R in H0.
        replace (length tvs - length tvs) with 0 in H0 by omega.
        simpl in *. inversion H0. subst; auto.
        omega. }
      { intros. apply nat_compare_lt in H1.
        simpl.
        rewrite nth_error_app_R in H0 by omega.
        rewrite nth_error_app_R by omega.
        change (t :: tvs') with ((t :: nil) ++ tvs') in H0.
        rewrite nth_error_app_R in H0. 2: simpl; omega.
        simpl in *. rewrite <- H0. f_equal. omega. }
      { intros. apply nat_compare_gt in H1.
        simpl. rewrite nth_error_app_L in * by omega. assumption. } }
    { eapply (IHe (lift 0 1 w) tvs' (t0 :: tvs)) in H0; eauto.
      simpl in *. rewrite H0. reflexivity.
      simpl.
      generalize (typeof_expr_lift tus w nil (t0 :: nil) (tvs ++ tvs')).
      simpl.
      intro. rewrite H1. assumption. }
  Qed.

  Theorem substitute_one_sound
  : forall tus e tvs w e',
      substitute_one (length tvs) w e = e' ->
      forall tvs' (t t' : typ),
        match lambda_exprD tus (tvs ++ tvs') t w
            , lambda_exprD tus (tvs ++ t :: tvs') t' e
        with
          | Some wval , Some eval =>
            match lambda_exprD tus (tvs ++ tvs') t' e' with
              | None => False
              | Some val' =>
                forall (us : hlist _ tus) (gs : hlist typD tvs) (gs' : hlist typD tvs'),
                  eval us (hlist_app gs (Hcons (wval us (hlist_app gs gs')) gs')) =
                  val' us (hlist_app gs gs')
            end
          | _ , _ => True
        end.
  Proof.
    induction e; simpl; intros; autorewrite with exprD_rw; simpl;
    forward; inv_all; subst.
    { simpl. consider (nat_compare (length tvs) v); intros.
      { apply nat_compare_eq in H. subst.
        eapply nth_error_get_hlist_nth_Some in H2.
        destruct H2. simpl in *.
        generalize x0.
        rewrite nth_error_app_R by omega.
        replace (length tvs - length tvs) with 0 by omega.
        simpl. inversion 1. subst. clear x1.
        destruct r. rewrite H0. intros.
        rewrite H. unfold Rcast_val, Rcast, Relim. simpl.
        rewrite hlist_nth_hlist_app; eauto.
        generalize (cast1 tvs (x :: tvs') (length tvs)).
        generalize (cast2 tvs (x :: tvs') (length tvs)).
        clear - ED_typ.
        rewrite x0.
        replace (length tvs - length tvs) with 0 by omega.
        simpl in *.
        generalize dependent (e us (hlist_app gs gs')).
        generalize dependent (hlist_nth gs (length tvs)).
        gen_refl.
        cutrewrite (nth_error tvs (length tvs) = None).
        { intros. generalize (e1 e0). unfold value. uip_all'. reflexivity. }
        { rewrite nth_error_past_end; auto. } }
      { apply nat_compare_lt in H.
        autorewrite with exprD_rw; simpl.
        eapply nth_error_get_hlist_nth_appR in H2; simpl in *; [ | omega ].
        destruct H2.
        consider (v - length tvs).
        { intro. exfalso. omega. }
        { intros. assert (n = (v - 1) - length tvs) by omega; subst.
          forward.
          assert (v - 1 >= length tvs) by omega.
          consider (nth_error_get_hlist_nth typD (tvs ++ tvs') (v - 1)); intros.
          { eapply nth_error_get_hlist_nth_appR in H7; eauto.
            forward_reason. rewrite H4 in H7.
            inv_all; subst. subst. destruct s0; simpl in *.
            rewrite H3. intros. rewrite H8. rewrite H9. reflexivity. }
          { clear - H7 H4.
            eapply nth_error_get_hlist_nth_None in H7.
            eapply nth_error_get_hlist_nth_Some in H4. simpl in *.
            destruct H4. clear H.
            eapply nth_error_length_ge in H7.
            eapply nth_error_length_lt in x.
            rewrite app_length in H7. omega. } } }
      { apply nat_compare_gt in H.
        autorewrite with exprD_rw; simpl.
        assert (v < length tvs) by omega.
        generalize H1.
        eapply (@nth_error_get_hlist_nth_appL _ typD (t :: tvs')) in H1.
        intro.
        eapply (@nth_error_get_hlist_nth_appL _ typD tvs') in H4.
        forward_reason. Cases.rewrite_all_goal.
        destruct x0; simpl in *.
        rewrite H7 in H5. inv_all; subst. destruct r.
        repeat match goal with
                 | H : _ |- _ => eapply nth_error_get_hlist_nth_Some in H
               end; simpl in *; forward_reason.
        unfold Rcast_val, Rcast in *; simpl in *.
        consider (type_cast (projT1 x1) x).
        { intros. red in r. subst. simpl.
          rewrite H2; clear H2.
          rewrite H4; clear H4.
          clear - ED_typ H.
          rewrite hlist_nth_hlist_app; eauto. symmetry.
          rewrite hlist_nth_hlist_app; eauto.
          gen_refl.
          generalize dependent (hlist_nth gs v).
          generalize (hlist_nth gs' (v - length tvs)).
          generalize (hlist_nth (Hcons (e us (hlist_app gs gs')) gs')
                                (v - length tvs)).
          generalize (cast1 tvs (t :: tvs') v).
          generalize (cast2 tvs (t :: tvs') v).
          generalize (cast2 tvs tvs' v).
          generalize (cast1 tvs tvs' v).
          consider (nth_error tvs v).
          { intros. generalize (e3 t0 e4).
            generalize (e3 t0 e4). uip_all'.
            clear - ED_typ. assert (t0 = projT1 x1) by congruence. subst.
            uip_all'. reflexivity. }
          { intros.
            eapply nth_error_length_ge in H0. exfalso. omega. } }
        { intros. eapply type_cast_total in H7; eauto.
          apply H7. clear - x3 x5 H.
          rewrite nth_error_app_L in * by omega.
          rewrite x5 in x3. congruence. } } }
    { simpl. autorewrite with exprD_rw.
      unfold symAs in *.
      generalize dependent (symD f).
      destruct (typeof_sym f).
      { intros.
        forward. }
      { congruence. } }
    { autorewrite with exprD_rw. simpl.
      erewrite substitute_one_typed; eauto.
      { specialize (IHe2 tvs w _ eq_refl tvs' t t0).
        specialize (IHe1 tvs w _ eq_refl tvs' t (typ2 t0 t')).
        revert IHe1 IHe2.
        Cases.rewrite_all_goal. intros; forward.
        unfold AbsAppI.exprT_App.
        autorewrite_with_eq_rw.
        rewrite IHe1. rewrite IHe2. reflexivity. }
      { eapply lambda_exprD_typeof_expr.
        left. eauto. } }
    { autorewrite with exprD_rw. simpl.
      destruct (typ2_match_case t').
      { destruct H as [ ? [ ? [ ? ? ] ] ].
        rewrite H in *; clear H.
        red in x1. subst. simpl in *.
        destruct (eq_sym (typ2_cast x x0)).
        forward. inv_all; subst.
        specialize (IHe (t :: tvs) (lift 0 1 w) _ eq_refl tvs' t0 x0).
        revert IHe. simpl.
        generalize (lambda_exprD_lift tus w nil (t :: nil) (tvs ++ tvs') t0).
        simpl. Cases.rewrite_all_goal.
        intros. forward.
        eapply functional_extensionality. intros.
        unfold Rcast_val, Rcast; simpl.
        inv_all; subst.
        specialize (IHe us (Hcons x1 gs)). simpl in *.
        specialize (H3 us Hnil). simpl in *.
        erewrite H3. instantiate (1 := Hcons x1 Hnil).
        eapply IHe. }
      { rewrite H in *. congruence. } }
    { autorewrite with exprD_rw. simpl.
      rewrite H2. rewrite H3. auto. }
  Qed.

End substitute.

Section beta.
  Context {typ : Set}.
  Context {sym : Set}.
  Context {RT : RType typ}
          {T2 : Typ2 _ RFun}
          {RS : RSym sym}
          {TD : EqDec _ (@eq typ)}.

  Context {RTOk : RTypeOk}
          {T2Ok : Typ2Ok T2}
          {RSOk : RSymOk RS}.

  (** This only beta-reduces the head term, i.e.
   ** (\ x . x) F ~> F
   ** F ((\ x . x) G) ~> F ((\ x . x) G)
   **)
  Fixpoint beta (e : expr typ sym) : expr typ sym :=
    match e with
      | App (Abs t e') e'' =>
        substitute_one 0 e'' e'
      | App a x =>
        App (beta a) x
      | e => e
    end.

  Theorem beta_sound
  : forall tus tvs e t,
      match lambda_exprD tus tvs t e with
        | None => True
        | Some val =>
          match lambda_exprD tus tvs t (beta e) with
            | None => False
            | Some val' =>
              forall us vs, val us vs = val' us vs
          end
      end.
  Proof.
    intros tus tvs e t.
    match goal with
      | |- ?G =>
        cut (lambda_exprD tus tvs t e = lambda_exprD tus tvs t e /\ G);
          [ intuition | ]
    end.
    revert tvs e t.
    refine (@ExprFacts.lambda_exprD_ind _ _ _ _ _ _ _ _
                                      (fun tus tvs e t val =>
                                         lambda_exprD tus tvs t e = val /\
                                      match val with
                                        | Some val =>
                                          match lambda_exprD tus tvs t (beta e) with
                                            | Some val' =>
                                              forall (us : hlist typD tus) (vs : hlist typD tvs),
                                                val us vs = val' us vs
                                            | None => False
                                          end
                                        | None => True
                                      end) _ _ _ _ _ _ _).
    { auto. }
    { simpl; intros; autorewrite with exprD_rw; Cases.rewrite_all_goal; simpl.
      rewrite type_cast_refl; eauto. }
    { simpl; intros; autorewrite with exprD_rw; Cases.rewrite_all_goal; simpl.
      rewrite type_cast_refl; eauto. }
    { simpl; intros; autorewrite with exprD_rw; Cases.rewrite_all_goal; simpl.
      unfold symAs. generalize (symD i).
      Cases.rewrite_all_goal.
      rewrite type_cast_refl; eauto. }
    { simpl. destruct f;
      simpl; intros; forward_reason;
      autorewrite with exprD_rw; Cases.rewrite_all_goal; simpl;
      forward; inv_all; subst.
      { split; auto. unfold AbsAppI.exprT_App.
        intros. autorewrite_with_eq_rw.
        rewrite H5. reflexivity. }
      { split; auto.
        clear H5. unfold AbsAppI.exprT_App.
        autorewrite_with_eq_rw.
        generalize (@substitute_one_sound _ _ _ _ _ _ _ _ _ tus f nil x _ eq_refl tvs d r).
        autorewrite with exprD_rw in H0. simpl in H0.
        rewrite typ2_match_iota in H0; eauto.
        rewrite eq_option_eq in H0.
        forward. inv_all; subst.
        simpl in *. destruct r0.
        rewrite H1 in H5. rewrite H6 in H5.
        forward.
        unfold AbsAppI.exprT_App, Rcast_val, Rcast, Relim.
        autorewrite_with_eq_rw.
        rewrite match_eq_sym_eq with (F:=fun x => x).
        simpl. specialize (H5 us Hnil vs).
        simpl in *. etransitivity; [ | eassumption ].
        reflexivity. } }
    { intros. forward_reason.
      forward. simpl.
      cutrewrite (lambda_exprD tus tvs (typ2 d r) (Abs d e) = Some (AbsAppI.exprT_Abs fval)); auto.
      autorewrite with exprD_rw.
      rewrite typ2_match_iota; auto.
      rewrite type_cast_refl; auto. simpl.
      rewrite H. unfold AbsAppI.exprT_Abs.
      autorewrite with eq_rw. reflexivity. }
  Qed.

End beta.
