Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.Lambda.ExprD.
Require Import MirrorCore.Lambda.ExprTac.

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

  Fixpoint vars_to_uvars (skip add : nat) (e : expr typ func) : expr typ func :=
    match e with
      | Var v =>
        if v ?[ lt ] skip then Var v
        else UVar (v - skip + add)
      | UVar _
      | Inj _ => e
      | App l r => App (vars_to_uvars skip add l) (vars_to_uvars skip add r)
      | Abs t e => Abs t (vars_to_uvars (S skip) add e)
    end.

End raw_types.

Section types.
  Context {typ : Type}.
  Context {func : Type}.
  Context {RType_typD : RType typ}.
  Context {Typ2_Fun : Typ2 RType_typD Fun}.
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
  Proof.
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

  Theorem exprD'_lower
  : forall tus tvs tvs' tvs'' e t val e',
      lower (length tvs) (length tvs') e = Some e' ->
      exprD' tus (tvs ++ tvs' ++ tvs'') t e = Some val ->
      exists val',
        exprD' tus (tvs ++ tvs'') t e' = Some val' /\
        forall us vs vs' vs'',
          val us (hlist_app vs (hlist_app vs' vs'')) =
          val' us (hlist_app vs vs'').
  Proof.
    intros tus tvs tvs' tvs'' e. revert tvs.
    induction e; simpl; intros;
    autorewrite with exprD_rw in *; simpl in *; forward; inv_all; subst.
    { consider (v ?[ lt ] length tvs); intros; forward.
      { inv_all; subst.
        autorewrite with exprD_rw. simpl.
        generalize H.
        eapply nth_error_get_hlist_nth_appL with (F := typD) (tvs' := tvs' ++ tvs'') in H.
        intro.
        eapply nth_error_get_hlist_nth_appL with (F := typD) (tvs' := tvs'') in H0.
        forward_reason; Cases.rewrite_all_goal.
        destruct x0; simpl in *.
        rewrite H3 in *. rewrite H1 in *. inv_all; subst.
        simpl in *. rewrite H2. eexists; split; eauto.
        intros. simpl. rewrite H6. rewrite H4. reflexivity. }
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
      unfold exprT_App.
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
  Proof.
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

  Theorem exprD'_lift
  : forall tus e tvs tvs' tvs'' t,
      match exprD' tus (tvs ++ tvs'') t e with
        | None => True
        | Some val =>
          match exprD' tus (tvs ++ tvs' ++ tvs'') t (lift (length tvs) (length tvs') e) with
            | None => False
            | Some val' =>
              forall us vs vs' vs'',
                val us (hlist_app vs vs'') =
                val' us (hlist_app vs (hlist_app vs' vs''))
          end
      end.
  Proof.
    induction e; simpl; intros; autorewrite with exprD_rw; simpl;
    forward; inv_all; subst; Cases.rewrite_all_goal; auto.
    { consider (v ?[ lt ] length tvs); intros.
      { generalize H.
        eapply nth_error_get_hlist_nth_appL with (tvs' := tvs' ++ tvs'') (F := typD) in H; eauto with typeclass_instances.
        intro.
        eapply nth_error_get_hlist_nth_appL with (tvs' := tvs'') (F := typD)
          in H2; eauto with typeclass_instances.
        forward_reason.
        revert H2. Cases.rewrite_all_goal. destruct x1.
        simpl in *. intros.
        destruct r. rewrite H5 in *.
        inv_all; subst. simpl in *.
        rewrite type_cast_refl; eauto.
        intros.
        rewrite H4. rewrite H6. auto. }
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
      unfold exprT_App.
      autorewrite with eq_rw.
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

  Theorem vars_to_uvars_typeof_expr
  : forall tus e tvs tvs' t,
      typeof_expr tus (tvs ++ tvs') e = Some t ->
      typeof_expr (tus ++ tvs') tvs (vars_to_uvars (length tvs) (length tus) e)
      = Some t.
  Proof.
    induction e; simpl; intros; auto.
    { consider (v ?[ lt ] length tvs); intros.
      { simpl. rewrite ListNth.nth_error_app_L in H; auto. }
      { simpl. rewrite ListNth.nth_error_app_R in H; auto. 2: omega.
        rewrite ListNth.nth_error_app_R; try omega.
        replace (v - length tvs + length tus - length tus) with (v - length tvs)
          by omega.
        auto. } }
    { forward. erewrite IHe1; eauto. erewrite IHe2; eauto. }
    { forward. eapply (IHe (t :: tvs) tvs') in H.
      simpl in *.
      rewrite H in *. auto. }
    { apply ListNth.nth_error_weaken; auto. }
  Qed.

  Lemma nth_error_get_hlist_nth_rwR
  : forall {T} (F : T -> _) tus tvs' n,
      n >= length tus ->
      match nth_error_get_hlist_nth F tvs' (n - length tus) with
        | None => True
        | Some (existT t v) =>
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
      clear H1. eapply ListNth.nth_error_length_lt in x0.
      rewrite app_length in H0. omega. }
  Qed.

  Definition lem_vars_to_uvars_exprD' : Prop :=
    forall (tus : tenv typ) (e : _) (tvs : list typ)
         (t : typ) (tvs' : list typ)
         (val : hlist typD tus ->
                hlist typD (tvs ++ tvs') -> typD t),
    exprD' tus (tvs ++ tvs') t e = Some val ->
    exists
      val' : hlist typD (tus ++ tvs') ->
             hlist typD tvs -> typD t,
      exprD' (tus ++ tvs') tvs t (vars_to_uvars (length tvs) (length tus) e) = Some val' /\
      (forall (us : hlist typD tus)
              (vs' : hlist typD tvs') (vs : hlist typD tvs),
         val us (hlist_app vs vs') = val' (hlist_app us vs') vs).

  Theorem vars_to_uvars_exprD' : lem_vars_to_uvars_exprD'.
  Proof.
    red.
    induction e; simpl; intros.
    { revert H; consider (v ?[ lt ] length tvs);
      autorewrite with exprD_rw; simpl; intros; forwardy.
      { inv_all; subst.
        eapply nth_error_get_hlist_nth_appL in H.
        forward_reason. rewrite H2.
        rewrite H in H0. inv_all; subst.
        simpl in *. change_rewrite H1.
        eexists; split; try reflexivity.
        simpl. intros. f_equal. apply H3. }
      { inv_all; subst.
        eapply nth_error_get_hlist_nth_appR in H0.
        2: omega.
        simpl in *.
        forward_reason.
        assert (v - length tvs + length tus >= length tus) by omega.
        eapply nth_error_get_hlist_nth_rwR with (F := typD) in H3.
        revert H3.
        instantiate (1 := tvs').
        cutrewrite (v - length tvs + length tus - length tus = v - length tvs); [ | omega ].
        change_rewrite H0.
        intros; forward_reason.
        change_rewrite H3.
        change_rewrite H1.
        eexists; split; try reflexivity.
        simpl. intros. f_equal. rewrite H2. eapply H4. } }
    { revert H; autorewrite with exprD_rw; simpl.
      intros. destruct (funcAs f t); try congruence.
      eexists; split; try reflexivity.
      simpl. inv_all; subst. reflexivity. }
    { revert H. autorewrite with exprD_rw; simpl; intros.
      forwardy; inv_all; subst.
      eapply vars_to_uvars_typeof_expr in H.
      change_rewrite H.
      eapply IHe1 in H0.
      eapply IHe2 in H1.
      forward_reason.
      Cases.rewrite_all_goal.
      eexists; split; try reflexivity.
      intros.
      unfold exprT_App.
      autorewrite with eq_rw.
      rewrite H2. rewrite H3. reflexivity. }
    { revert H. autorewrite with exprD_rw; simpl; intros.
      match goal with
        | H : typ2_match _ ?Y _ _ = _ |- _ =>
          arrow_case Y
      end; try congruence.
      clear H0.
      red in x1; subst. unfold Relim in *.
      autorewrite with eq_rw in *. forwardy.
      change_rewrite H.
      destruct y0. eapply IHe with (tvs := x :: tvs) in H1.
      forward_reason.
      change_rewrite H1.
      eexists; split; try reflexivity.
      inv_all; subst. intros.
      autorewrite with eq_rw.
      eapply match_eq_match_eq with (F := fun x => x).
      eapply FunctionalExtensionality.functional_extensionality.
      intros. specialize (H3 us vs' (Hcons x2 vs)).
      apply H3. }
    { revert H. autorewrite with exprD_rw; simpl; intros.
      forwardy. inv_all; subst.
      eapply nth_error_get_hlist_nth_weaken in H.
      simpl in *. forward_reason.
      rewrite H. change_rewrite H0.
      eexists; split; try reflexivity.
      simpl. intros. f_equal. apply H1. }
  Qed.

End types.