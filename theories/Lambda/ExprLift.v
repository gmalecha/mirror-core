Require Import Coq.omega.Omega.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Tactics.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.AbsAppI.
Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.Util.Compat.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprD.

Set Implicit Arguments.
Set Strict Implicit.

Section raw_types.
  Context {typ func : Type}.

  Fixpoint lower (skip : nat) (_by : nat) (e : expr typ func) {struct e}
  : option (expr typ func) :=
    match e with
      | Var v => if v ?[ lt ] skip then Some (Var v)
                 else if (v - skip) ?[ lt ] _by then None
                      else Some (Var (v - _by))
      | Inj f => Some (Inj f)
      | UVar u => Some (UVar u)
      | App a b =>
        ap (ap (pure App) (lower skip _by a)) (lower skip _by b)
      | Abs t a =>
        ap (pure (Abs t)) (lower (S skip) _by a)
    end.

  Fixpoint lift (skip : nat) (_by : nat) (e : expr typ func) {struct e}
  : expr typ func :=
    match e with
      | Var v => Var (if v ?[ lt ] skip then v else (v + _by))
      | Inj f => Inj f
      | UVar u => UVar u
      | App a b =>
        App (lift skip _by a) (lift skip _by b)
      | Abs t a =>
        Abs t (lift (S skip) _by a)
    end.

End raw_types.

Section types.
  Context {typ : Type}.
  Context {func : Type}.
  Context {RType_typD : RType typ}.
  Context {Typ2_Fun : Typ2 RType_typD RFun}.
  Context {RSym_func : RSym func}.

  (** Reasoning principles **)
  Context {RTypeOk_typD : RTypeOk}.
  Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.
  Context {RSymOk_func : RSymOk RSym_func}.

  Theorem typeof_expr_lower
  : forall tus e tvs tvs' tvs'' e',
      lower (length tvs) (length tvs') e = Some e' ->
      typeof_expr tus (tvs ++ tvs'') e' =
      typeof_expr tus (tvs ++ tvs' ++ tvs'') e.
  Proof using.
    intros tus e tvs tvs' tvs''; revert tvs.
    induction e; simpl; intros; simpl in *; forward; inv_all; subst; auto.
    { consider (v ?[ lt ] length tvs); intros; forward; inv_all; subst.
      { simpl.
        repeat rewrite ListNth.nth_error_app_L by omega. reflexivity. }
      { simpl.
        repeat rewrite ListNth.nth_error_app_R by omega.
        f_equal. omega. } }
    { eapply IHe1 in H. eapply IHe2 in H0.
      simpl. rewrite H0. rewrite H. reflexivity. }
    { simpl. specialize (IHe (t :: tvs)).
      simpl in *. eapply IHe in H.
      destruct H. reflexivity. }
  Qed.

  Theorem lambda_exprD_lower
  : forall tus tvs tvs' tvs'' e t val e',
      lower (length tvs) (length tvs') e = Some e' ->
      lambda_exprD tus (tvs ++ tvs' ++ tvs'') t e = Some val ->
      exists val',
        lambda_exprD tus (tvs ++ tvs'') t e' = Some val' /\
        forall us vs vs' vs'',
          val us (hlist_app vs (hlist_app vs' vs'')) =
          val' us (hlist_app vs vs'').
  Proof using RTypeOk_typD RSymOk_func Typ2Ok_Fun.
    intros tus tvs tvs' tvs'' e. revert tvs.
    induction e; simpl; intros;
    autorewrite with exprD_rw in *; simpl in *; forward; inv_all; subst.
    { consider (v ?[ lt ] length tvs); intros; forward.
      { inv_all; subst.
        autorewrite with exprD_rw. simpl.
        generalize (@nth_error_get_hlist_nth_appL _ typD (tvs' ++ tvs'') _ _ H).
        generalize (@nth_error_get_hlist_nth_appL _ typD tvs'' _ _ H).
        intros.
        forward_reason; Cases.rewrite_all_goal.
        rewrite H6 in *.
        inv_all. subst.
        destruct x0; destruct x1; simpl in *.
        rewrite H3 in *. rewrite H1 in *. inv_all; subst.
        simpl in *. rewrite H2. eexists; split; eauto.
        intros. simpl. rewrite H7. rewrite H5. reflexivity. }
      { inv_all; subst.
        autorewrite with exprD_rw. simpl.
        consider (nth_error_get_hlist_nth typD (tvs ++ tvs'') (v - length tvs')); intros.
        { destruct s.
          eapply nth_error_get_hlist_nth_appR in H1; [ simpl in * | omega ].
          destruct H1 as [ ? [ ? ? ] ].
          eapply nth_error_get_hlist_nth_appR in H1; [ simpl in * | omega ].
          eapply nth_error_get_hlist_nth_appR in H3; [ simpl in * | omega ].
          forward_reason.
          replace (v - length tvs' - length tvs)
             with (v - length tvs - length tvs') in H3 by omega.
          rewrite H1 in *. inv_all; subst. rewrite H2.
          eexists; split; eauto. intros.
          rewrite H4. rewrite H6. rewrite H5. reflexivity. }
        { exfalso.
          rewrite nth_error_get_hlist_nth_None in H3.
          eapply nth_error_get_hlist_nth_Some in H1. destruct H1. clear H1.
          simpl in *.
          repeat rewrite ListNth.nth_error_app_R in * by omega.
          replace (v - length tvs' - length tvs)
             with (v - length tvs - length tvs') in H3 by omega.
          congruence. } } }
    { autorewrite with exprD_rw. rewrite H0. simpl. eauto. }
    { autorewrite with exprD_rw.
      generalize H4.
      eapply typeof_expr_lower in H4; rewrite H4; clear H4.
      rewrite H0. simpl. intro.
      eapply IHe1 in H; eauto.
      eapply IHe2 in H4; eauto.
      forward_reason.
      Cases.rewrite_all_goal.
      eexists; split; eauto. intros.
      unfold AbsAppI.exprT_App.
      match goal with
        | |- match ?X with _ => _ end _ _ _ _ =
             match ?Y with _ => _ end _ _ _ _ =>
          change Y with X ; generalize X
      end; intros.
      autorewrite with eq_rw.
      clear - H4 H5. destruct e3; simpl.
      rewrite H5. rewrite H4. reflexivity. }
    { autorewrite with exprD_rw in *; simpl in *.
      destruct (typ2_match_case t0).
      { destruct H1 as [ ? [ ? [ ? ? ] ] ].
        rewrite H1 in *; clear H1.
        generalize dependent (typ2_cast x x0).
        destruct x1. simpl in *. intros.
        specialize (IHe (t :: tvs)). simpl in *.
        repeat first [ rewrite eq_option_eq in *
                     | rewrite eq_Const_eq in *
                     | rewrite eq_Arr_eq in * ].
        forward; inv_all; subst.
        eapply IHe in H2; eauto.
        forward_reason; Cases.rewrite_all_goal.
        simpl. eexists; split; eauto.
        intros. eapply FunctionalExtensionality.functional_extensionality.
        intros.
        specialize (H2 us (Hcons x2 vs)).
        simpl in H2. rewrite H2. reflexivity. }
      { rewrite H1 in *. congruence. } }
    { autorewrite with exprD_rw. rewrite H1. simpl.
      rewrite H2. eauto. }
  Qed.

  Theorem typeof_expr_lift
  : forall tus e tvs tvs' tvs'',
      typeof_expr tus (tvs ++ tvs' ++ tvs'') (lift (length tvs) (length tvs') e) =
      typeof_expr tus (tvs ++ tvs'') e.
  Proof using.
    intros tus e tvs; revert tvs; induction e; simpl; intros;
    Cases.rewrite_all_goal; auto.
    { consider (v ?[ lt ] length tvs); intros.
      { repeat rewrite ListNth.nth_error_app_L by auto.
        reflexivity. }
      { repeat rewrite ListNth.nth_error_app_R by omega.
        f_equal. omega. } }
    { specialize (IHe (t :: tvs)). simpl in *.
      rewrite IHe. reflexivity. }
  Qed.

  Theorem lambda_exprD_lift
  : forall tus e tvs tvs' tvs'' t,
      match lambda_exprD tus (tvs ++ tvs'') t e with
        | None => True
        | Some val =>
          match lambda_exprD tus (tvs ++ tvs' ++ tvs'') t (lift (length tvs) (length tvs') e) with
            | None => False
            | Some val' =>
              forall us vs vs' vs'',
                val us (hlist_app vs vs'') =
                val' us (hlist_app vs (hlist_app vs' vs''))
          end
      end.
  Proof using RTypeOk_typD RSymOk_func Typ2Ok_Fun.
    induction e; simpl; intros; autorewrite with exprD_rw; simpl;
    forward; inv_all; subst; Cases.rewrite_all_goal; auto.
    { consider (v ?[ lt ] length tvs); intros.
      { generalize (@nth_error_get_hlist_nth_appL _ typD (tvs' ++ tvs'') _ _ H).
        generalize (@nth_error_get_hlist_nth_appL _ typD tvs'' _ _ H).
        clear H. intros.
        forward_reason.
        revert H3. revert H0. Cases.rewrite_all_goal. destruct x1.
        intros; simpl in *. destruct x0; simpl in *.
        inv_all. subst.
        Cases.rewrite_all_goal.
        intros.
        rewrite H4. rewrite H6. reflexivity. }
      { eapply nth_error_get_hlist_nth_appR in H0; [ simpl in * | omega ].
        forward_reason.
        consider (nth_error_get_hlist_nth typD (tvs ++ tvs' ++ tvs'')
           (v + length tvs')); intros.
        { destruct s. forward.
          eapply nth_error_get_hlist_nth_appR in H3; [ simpl in * | omega ].
          forward_reason.
          eapply nth_error_get_hlist_nth_appR in H3; [ simpl in * | omega ].
          forward_reason.
          replace (v + length tvs' - length tvs - length tvs')
             with (v - length tvs) in H3 by omega.
          rewrite H0 in *. inv_all; subst.
          rewrite H1. congruence. }
        { rewrite nth_error_get_hlist_nth_None in H3.
          eapply nth_error_get_hlist_nth_Some in H0. destruct H0.
          clear H0. simpl in *.
          repeat rewrite ListNth.nth_error_app_R in H3 by omega.
          replace (v + length tvs' - length tvs - length tvs')
             with (v - length tvs) in H3 by omega.
          congruence. } } }
    { rewrite typeof_expr_lift. rewrite H.
      specialize (IHe1 tvs tvs' tvs'' (typ2 t0 t)).
      specialize (IHe2 tvs tvs' tvs'' t0).
      forward. inv_all. subst.
      unfold AbsAppI.exprT_App.
      autorewrite_with_eq_rw.
      rewrite <- IHe1. rewrite <- IHe2. reflexivity. }
    { destruct (typ2_match_case t0).
      { destruct H0 as [ ? [ ? [ ? ? ] ] ].
        rewrite H0 in *; clear H0.
        generalize dependent (typ2_cast x x0).
        destruct x1. simpl.
        intros. rewrite eq_option_eq in *.
        forward. inv_all; subst.
        specialize (IHe (t :: tvs) tvs' tvs'' x0).
        revert IHe. simpl. Cases.rewrite_all_goal.
        intros; forward.
        eapply FunctionalExtensionality.functional_extensionality.
        intros. eapply (IHe us (Hcons x1 vs)). }
      { rewrite H0 in *. congruence. } }
  Qed.

End types.