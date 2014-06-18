Require Import Coq.Arith.Compare_dec.
Require Import ExtLib.Data.Pair.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SymI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Lambda.TypesI2.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.Lambda.AppN.

Require Import FunctionalExtensionality.

Set Implicit Arguments.
Set Strict Implicit.

Section substitute.
  Context {sym : Type}.
  Context {RT : RType}
          {T2 : Typ2 _ PreFun.Fun}
          {RS : RSym typD sym}.

  Context {RTOk : RTypeOk RT}
          {T2Ok : Typ2Ok T2}
          {RSOk : RSymOk RS}.

  Context {ED_typ : EqDec _ (@eq typ)}.

  Fixpoint substitute' (v : var) (w : expr typ sym) (e : expr typ sym)
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
      | App l' r' => App (substitute' v w l') (substitute' v w r')
      | Abs t e => Abs t (substitute' (S v) (lift 0 1 w) e)
    end.

  Theorem substitute'_typed
  : forall ts tus t e w tvs' tvs t',
      typeof_expr ts tus (tvs ++ tvs') w = Some t ->
      typeof_expr ts tus (tvs ++ t :: tvs') e = Some t' ->
      typeof_expr ts tus (tvs ++ tvs') (substitute' (length tvs) w e) = Some t'.
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
      generalize (typeof_expr_lift ts tus w nil (t0 :: nil) (tvs ++ tvs')).
      simpl.
      intro. rewrite H1. assumption. }
  Qed.

  Theorem substitute'_sound
  : forall ts tus e tvs w e',
      substitute' (length tvs) w e = e' ->
      forall tvs' (t t' : typ),
        match exprD' ts tus (tvs ++ tvs') t w
            , exprD' ts tus (tvs ++ t :: tvs') t' e
        with
          | Some wval , Some eval =>
            match exprD' ts tus (tvs ++ tvs') t' e' with
              | None => False
              | Some val' =>
                forall (us : hlist _ tus) (gs : hlist (typD ts) tvs) (gs' : hlist (typD ts) tvs'),
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
        generalize dependent (o us (hlist_app gs gs')).
        generalize dependent (hlist_nth gs (length tvs)).
        gen_refl.
        cutrewrite (nth_error tvs (length tvs) = None).
        { intros. generalize (e0 e). unfold value. uip_all'. reflexivity. }
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

          eapply (@nth_error_get_hlist_nth_rwR _ (typD ts) tvs tvs') in H6.
          rewrite H4 in *. forward_reason.
          rewrite H6. subst. inv_all; subst. subst.
          destruct r. rewrite type_cast_refl; eauto.
          intros. f_equal. rewrite H8. apply H7. } }
      { apply nat_compare_gt in H.
        autorewrite with exprD_rw; simpl.
        assert (v < length tvs) by omega.
        generalize H1.
        eapply (@nth_error_get_hlist_nth_appL _ (typD ts) (t :: tvs')) in H1.
        intro.
        eapply (@nth_error_get_hlist_nth_appL _ (typD ts) tvs') in H4.
        forward_reason. Cases.rewrite_all_goal.
        destruct x0; simpl in *.
        rewrite H7 in H5. inv_all; subst. destruct r.
        repeat match goal with
                 | H : _ |- _ => eapply nth_error_get_hlist_nth_Some in H
               end; simpl in *; forward_reason.
        unfold Rcast_val, Rcast in *; simpl in *.
        consider (type_cast ts (projT1 x1) x).
        { intros. red in r. subst. simpl.
          rewrite H2; clear H2.
          rewrite H4; clear H4.
          clear - ED_typ H.
          rewrite hlist_nth_hlist_app; eauto. symmetry.
          rewrite hlist_nth_hlist_app; eauto.
          gen_refl.
          generalize dependent (hlist_nth gs v).
          generalize (hlist_nth gs' (v - length tvs)).
          generalize (hlist_nth (Hcons (o us (hlist_app gs gs')) gs')
                                (v - length tvs)).
          generalize (cast1 tvs (t :: tvs') v).
          generalize (cast2 tvs (t :: tvs') v).
          generalize (cast2 tvs tvs' v).
          generalize (cast1 tvs tvs' v).
          consider (nth_error tvs v).
          { intros. generalize (e t0 e3).
            generalize (e2 t0 e3). uip_all'.
            clear - ED_typ. assert (t0 = projT1 x1) by congruence. subst.
            uip_all'. reflexivity. }
          { intros.
            eapply nth_error_length_ge in H0. exfalso. omega. } }
        { intros. eapply type_cast_total in H7; eauto.
          apply H7. clear - x3 x5 H.
          rewrite nth_error_app_L in * by omega.
          rewrite x5 in x3. congruence. } } }
    { simpl. autorewrite with exprD_rw.
      unfold funcAs in *.
      generalize dependent (symD f).
      destruct (typeof_sym f).
      { intros.
        forward. destruct r.
        simpl in *. unfold Rcast in H1. simpl in *. inv_all; subst; auto. }
      { congruence. } }
    { autorewrite with exprD_rw. simpl.
      erewrite substitute'_typed; eauto.
      { specialize (IHe2 tvs w _ eq_refl tvs' t t0).
        specialize (IHe1 tvs w _ eq_refl tvs' t (typ2 t0 t')).
        revert IHe1 IHe2.
        Cases.rewrite_all_goal. intros; forward.
        unfold Open_App, OpenT, ResType.OpenT.
        repeat first [ rewrite eq_Const_eq | rewrite eq_Arr_eq ].
        rewrite IHe1. rewrite IHe2. reflexivity. }
      { eapply exprD'_typeof_expr.
        left. eauto. } }
    { autorewrite with exprD_rw. simpl.
      destruct (typ2_match_case ts t').
      { destruct H as [ ? [ ? [ ? ? ] ] ].
        rewrite H in *; clear H.
        red in x1. subst. simpl in *.
        destruct (eq_sym (typ2_cast ts x x0)).
        forward. inv_all; subst.
        specialize (IHe (t :: tvs) (lift 0 1 w) _ eq_refl tvs' t0 x0).
        revert IHe. simpl.
        generalize (exprD'_lift ts tus w nil (t :: nil) (tvs ++ tvs') t0).
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
  Context {sym : Type}.
  Context {RT : RType}
          {T2 : Typ2 _ PreFun.Fun}
          {RS : RSym typD sym}.

  Context {RTOk : RTypeOk RT}
          {T2Ok : Typ2Ok T2}
          {RSOk : RSymOk RS}.

  (** This only beta-reduces the head term, i.e.
   ** (\ x . x) F ~> F
   ** F ((\ x . x) G) ~> F ((\ x . x) G)
   **)
  Fixpoint beta (e : expr typ sym) : expr typ sym :=
    match e with
      | App (Abs t e') e'' =>
        substitute' 0 e'' e'
      | App a x =>
        App (beta a) x
      | e => e
    end.

  Theorem beta_sound
  : forall ts tus tvs e t,
      match exprD' ts tus tvs t e with
        | None => True
        | Some val =>
          match exprD' ts tus tvs t (beta e) with
            | None => False
            | Some val' =>
              forall us vs, val us vs = val' us vs
          end
      end.
  Proof.
    intros ts tus tvs e t.
    match goal with
      | |- ?G =>
        cut (exprD' ts tus tvs t e = exprD' ts tus tvs t e /\ G);
          [ intuition | ]
    end.
    revert tvs e t.
    refine (@ExprFacts.exprD'_ind _ _ _ _ _ _ _
                                      (fun ts tus tvs e t val =>
                                         exprD' ts tus tvs t e = val /\
                                      match val with
                                        | Some val =>
                                          match exprD' ts tus tvs t (beta e) with
                                            | Some val' =>
                                              forall (us : hlist (typD ts) tus) (vs : hlist (typD ts) tvs),
                                                val us vs = val' us vs
                                            | None => False
                                          end
                                        | None => True
                                      end) _ _ _ _ _ _ _ _).
    { auto. }
    { simpl; intros; autorewrite with exprD_rw; Cases.rewrite_all_goal; simpl.
      rewrite type_cast_refl; eauto. }
    { simpl; intros; autorewrite with exprD_rw; Cases.rewrite_all_goal; simpl.
      rewrite type_cast_refl; eauto. }
    { simpl; intros; autorewrite with exprD_rw; Cases.rewrite_all_goal; simpl.
      unfold funcAs. generalize (symD i).
      Cases.rewrite_all_goal.
      rewrite type_cast_refl; eauto. simpl. auto. }
    { simpl. destruct f;
      simpl; intros; forward_reason;
      autorewrite with exprD_rw; Cases.rewrite_all_goal; simpl;
      forward; inv_all; subst.
      { split; auto. unfold Open_App.
        intros.
        unfold OpenT, ResType.OpenT.
        repeat first [ rewrite eq_Const_eq | rewrite eq_Arr_eq ].
        rewrite H5. reflexivity. }
      { split; auto.
        clear H5. unfold Open_App.
        repeat first [ rewrite eq_Const_eq | rewrite eq_Arr_eq ].
        generalize (@substitute'_sound).
        admit. } }
    { intros. forward_reason.
      forward. simpl.
      cutrewrite (exprD' ts tus tvs (typ2 d r) (Abs d e) = Some (Open_Abs fval)); auto.
      autorewrite with exprD_rw.
      rewrite typ2_match_zeta; auto.
      rewrite type_cast_refl; auto. simpl.
      rewrite H. unfold Open_Abs.
      rewrite eq_Arr_eq. rewrite eq_Const_eq.
      rewrite eq_option_eq. reflexivity. }
  Qed.

End beta.

Section beta_all.
  Context {sym : Type}.
  Context {RT : RType}
          {T2 : Typ2 _ PreFun.Fun}
          {RS : RSym typD sym}.

  Context {RTOk : RTypeOk _}
          {T2Ok : Typ2Ok T2}
          {RSOk : RSymOk RS}.

  Context {ED_typ : EqDec _ (@eq typ)}.

  (** NOTE: I should extend [delta] with [vars]
   ** - that means that its specification is exactly the same as [beta_all]
   **)
  Variable delta : expr typ sym -> list (expr typ sym) -> expr typ sym.

  Fixpoint beta_all
           (args : list (expr typ sym))
           (vars : list (option (expr typ sym)))
           (e : expr typ sym) : expr typ sym :=
    match e with
      | App e' e'' =>
        beta_all (beta_all nil vars e'' :: args) vars e'
      | Abs t e' =>
        match args with
          | nil => Abs t (beta_all nil (None :: vars) e') (** args = nil **)
          | a :: args => beta_all args (Some a :: vars) e'
        end
      | Var v =>
        delta match nth_error vars v with
                | Some (Some val) => lift 0 v val
                | Some None => Var v
                | None => Var (v - length vars)
              end args
      | e => delta e args
    end.

  (** default ext is apps **)
  Definition delta_sound
  := forall e es ts tus tvs t val,
       exprD' ts tus tvs t (apps e es) = Some val ->
       exists val',
         exprD' ts tus tvs t (delta e es) = Some val' /\
         forall us vs,
           val us vs = val' us vs.

  Hypothesis deltaOk : delta_sound.

  Variable ts : list Type.

  Inductive EnvForall {A} (R : A -> forall t : typ, typD ts t -> Prop)
  : list A -> forall tvs, hlist (typD ts) tvs -> Prop :=
  | EnvForall_nil : EnvForall R nil Hnil
  | EnvForall_cons : forall e es t ts v vs,
                       R e t v ->
                       @EnvForall A R es ts vs ->
                       @EnvForall A R (e :: es) (t :: ts) (Hcons v vs).

  Lemma Forall2_sem2
  : forall T U (P : T -> U -> Prop) xs ys,
      Forall2 P xs ys ->
      forall v y,
        nth_error ys v = Some y ->
        exists x, nth_error xs v = Some x /\
                  P x y.
  Proof.
    clear. induction 1; simpl; intros.
    { destruct v; inversion H. }
    { destruct v.
      { simpl in *. eexists; split; eauto.
        inversion H1. subst. auto. }
      { simpl in *. eauto. } }
  Qed.

  Section Forall2i.
    Variables T U : Type.

    Section def.
      Variable P : nat -> T -> U -> Prop.

      Inductive Forall2i : nat -> list T -> list U -> Prop :=
      | F2i_nil : forall n, Forall2i n nil nil
      | F2i_cons : forall x xs y ys n, P n x y ->
                                       Forall2i (S n) xs ys ->
                                       Forall2i n (x :: xs) (y :: ys).
    End def.

    Variable P Q : nat -> T -> U -> Prop.
    Lemma Forall2i_shift
    : forall m n xs ys,
        (forall n x y, P n x y -> Q (m + n) x y) ->
        Forall2i P n xs ys ->
        Forall2i Q (m + n) xs ys.
    Proof.
      clear. induction 2.
      { constructor. }
      { constructor; eauto.
        replace (m + S n) with (S (m + n)) in IHForall2i by omega.
        assumption. }
    Qed.
  End Forall2i.

(*
  Lemma beta_all_respectful
  : forall args args' vars vars' e e',
      Forall
      beta_all args vars e =
      beta_all args' vars' e'
*)

  Lemma eq_sym_eq_sym : forall T (a b : T) (pf : a = b),
                          eq_sym (eq_sym pf) = pf.
  Proof.
    clear. destruct pf. reflexivity.
  Qed.

  Lemma eq_eq_sym : forall T F (a b : T) (pf : a = b) (x : F b),
                      match pf in _ = t return F t with
                        | eq_refl =>
                          match eq_sym pf in _ = t return F t with
                            | eq_refl => x
                          end
                      end = x.
  Proof.
    clear. destruct pf. reflexivity.
  Qed.

  Lemma exprD'_App_Abs
  : forall ts tus tvs t t0 e ex val,
      exprD' ts tus tvs t0 (App (Abs t e) ex) = Some val ->
      exprD' ts tus tvs t0 (substitute' 0 ex e) = Some val.
  Proof.
    intros.
    autorewrite with exprD_rw in *; simpl in *.
    forward.
    autorewrite with exprD_rw in *; simpl in *.
    inv_all; subst.
    rewrite typ2_match_zeta in H0; eauto.
    rewrite eq_option_eq in H0.
    forward. inv_all; subst.
    destruct r.
    generalize (@substitute'_sound _ _ _ _ _ _ _ _ ts0 tus e nil ex _ eq_refl tvs t1 t0).
    simpl. Cases.rewrite_all_goal.
    intros. forward.
    f_equal. unfold Open_App.
    unfold OpenT, ResType.OpenT.
    repeat first [ rewrite eq_Const_eq | rewrite eq_Arr_eq ].
    clear - H4.
    apply functional_extensionality; intro.
    apply functional_extensionality; intro.
    repeat first [ rewrite eq_Const_eq | rewrite eq_Arr_eq ].
    specialize (H4 x Hnil x0).
    simpl in *.
    rewrite eq_sym_eq_sym. rewrite eq_eq_sym. auto.
  Qed.

  Theorem beta_all_sound
  : forall tus e tvs t val args vars,
      Forall2i (fun n t e => match e with
                               | None => True
                               | Some e =>
                                 exists val, exprD' ts tus (skipn n tvs) t e = Some val
                             end) 0 tvs vars ->
      exprD' ts tus tvs t (apps e args) = Some val ->
      exists val',
        exprD' ts tus tvs t (beta_all args vars e) = Some val' /\
        forall us vs,
          EnvForall (fun e t v =>
                       match e with
                         | None => True
                         | Some e =>
                           exists val, exprD' ts tus tvs t e = Some val /\
                           val us vs = v
                       end) vars vs ->
          val us vs = val' us vs.
  Proof.
    induction e; simpl; intros.
    { (*consider (nth_error vars v).
       { destruct o; intros.
        {           eapply Forall2_sem2 in H1; eauto. simpl in *.


        *) admit. }
    { eapply deltaOk in H0.
      destruct H0 as [ ? [ ? ? ] ].
      eexists; split; eauto. }
    { generalize H0.
      rewrite exprD'_apps in H0; eauto.
      unfold apps_sem' in H0.
      forward.
      autorewrite with exprD_rw in *; simpl in *; forward.
      change e2 with (apps e2 nil) in H5.
      eapply IHe2 with (vars := vars) in H5; eauto; clear IHe2.
      forward_reason.
      assert (exists val',
                exprD' ts tus tvs t (apps (App e1 (beta_all nil vars e2)) args) = Some val' /\
             forall us vs,
               EnvForall
                 (fun (e : option (expr typ sym)) (t3 : typ) (v : typD ts t3) =>
                    match e with
                      | Some e0 =>
                        exists val0 : OpenT ts tus tvs (typD ts t3),
                                      exprD' ts tus tvs t3 e0 = Some val0 /\ val0 us vs = v
                      | None => True
                    end) vars vs ->
               val us vs = val' us vs).
      { admit. }
      destruct H9 as [ ? [ ? ? ] ].
      change (apps (App e1 (beta_all nil vars e2)) args)
        with (apps e1 (beta_all nil vars e2 :: args)) in H9.
      eapply IHe1 in H9; eauto.
      forward_reason. eexists; split; eauto.
      intros. rewrite <- H11; eauto. }
    { destruct args.
      { simpl in *.
        autorewrite with exprD_rw in *; simpl in *.
        Require Import MirrorCore.Lambda.ExprTac.
        arrow_case ts t0.
        { clear H1. red in x1. subst. simpl in *.
          rewrite eq_option_eq in *.
          forward. inv_all; subst.
          change e with (apps e nil) in H2.
          eapply IHe with (vars := None :: vars) in H2; eauto.
          { admit. }
          { constructor; auto.
            revert H.
            eapply (@Forall2i_shift _ _ _ _ 1 0). intros.
            simpl; auto. } }
        { congruence. } }
      { simpl in *.
        rewrite exprD'_apps in H0; eauto.
        unfold apps_sem' in H0; eauto. forward.
        eapply exprD'_App_Abs in H1; eauto.
        admit. } }
    { eapply deltaOk in H0.
      forward_reason. eauto. }
  Qed.
End beta_all.
