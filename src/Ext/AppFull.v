Require Import Compare_dec.
Require Import ExtLib.Data.Pair.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SymI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.ExprLift.

Set Implicit Arguments.
Set Strict Implicit.

Section app_full.
  Variable ts : types.
  Variable sym : Type.
  Variable RSym_sym : RSym (typD ts) sym.

  Fixpoint apps (e : expr sym) (ls : list (expr sym)) :=
    match ls with
      | nil => e
      | l :: ls => apps (App e l) ls
    end.

  Fixpoint app_full' (e : expr sym) (acc : list (expr sym))
  : expr sym * list (expr sym) :=
    match e with
      | App l r =>
        app_full' l (r :: acc)
      | _ =>
        (e, acc)
    end.

  Definition app_full (e : expr sym) := app_full' e nil.

  Lemma apps_app_full'
  : forall e e' ls ls',
      app_full' e ls = (e', ls') ->
      apps e ls = apps e' ls'.
  Proof.
    induction e; simpl; intros; inv_all; subst; auto.
    eapply IHe1 in H. auto.
  Qed.

  Section app_sem.
    Variables us vs : env (typD ts).

    Fixpoint apply {T} (x : T) (ls : list {t : typ & T -> typD ts nil t}) t {struct ls} :
      typD ts nil (fold_left (fun x y => tyArr y x) (map (@projT1 _ _) ls) t) ->
      typD ts nil t :=
      match ls as ls
            return typD ts nil (fold_left (fun x y => tyArr y x)
                                          (map (@projT1 _ _) ls) t) ->
                   typD ts nil t
      with
        | nil => fun x => x
        | l :: ls => fun f => apply x ls (tyArr (projT1 l) t) f (projT2 l x)
      end.

    Fixpoint apply_sem
             (tf : typ) (e : typD ts nil tf)
             (ls : list (expr sym)) (t : typ)
             {struct ls}
    : option (typD ts nil t) :=
      match ls with
        | nil =>
          match typ_cast_typ ts nil tf t with
            | None => None
            | Some cast => Some (cast (fun x => x) e)
          end
        | l :: ls =>
          match tf as tf
                return typD ts nil tf -> _
          with
            | tyArr a b => fun f =>
                             match exprD us vs l a with
                               | None => None
                               | Some x => apply_sem b (f x) ls t
                             end
            | _ => fun _ => None
          end e
      end.

    Definition apps_sem
               (e : expr sym) (l : list (expr sym)) (t : typ)
    : option (typD ts nil t) :=
      match typeof_expr (typeof_env us) (typeof_env vs) e with
        | None => None
        | Some tf =>
          match exprD us vs e tf with
            | Some f => apply_sem _ f l t
            | None => None
          end
      end.

    Lemma apps_sem_nil : forall e t,
                           apps_sem e nil t = exprD us vs e t.
    Proof.
      intros. unfold apps_sem.
      consider (typeof_expr (typeof_env us) (typeof_env vs) e); intros.
      { eapply typeof_expr_exprD in H.
        destruct H. rewrite H.
        simpl.
        match goal with
          | |- match ?X with _ => _ end = _ =>
            consider X; intros
        end.
        { inv_all. subst. auto. }
        { rewrite exprD_type_cast in *.
          forward. inv_all.
          revert H3. subst. subst; intros.
          autorewrite with exprD_rw in *. congruence. } }
      { consider (exprD us vs e t); auto; intros.
        exfalso.
        assert (exists v, exprD us vs e t = Some v); eauto.
        eapply typeof_expr_exprD in H1. red in H1.
        congruence. }
    Qed.

    Lemma exprD_apps : forall es e t,
      exprD us vs (apps e es) t = apps_sem e es t.
    Proof.
      induction es; simpl; intros.
      { unfold apps_sem.
        rewrite exprD_type_cast. forward. }
      { rewrite IHes.
        unfold apps_sem.
        simpl. forward.
        consider (typeof_expr (typeof_env us) (typeof_env vs) a); intros.
        { destruct t0; forward.
          simpl.
          consider (typ_eqb t0_1 t1); intros; subst.
          { red_exprD. Cases.rewrite_all.
            forward. rewrite typ_cast_typ_refl. reflexivity. }
          { forward. exfalso.
            rewrite exprD_type_cast in H3.
            rewrite H0 in *.
            rewrite typ_cast_typ_neq in * by auto.
            congruence. } }
        { forward. subst.
          rewrite exprD_type_cast in H3. rewrite H0 in *. congruence. } }
    Qed.

(*
    Check apply_sem.

    Lemma apps_sem_cons : forall tf f t x e es,
                            @apply_sem tf f (e::es) t = x.
      simpl.
                            match tf 
                            match typeof_expr 
                            match exprD us vs f

    Lemma apps_app

    Lemma app_fullD : forall e e' es es' t,
                        app_full' e es = (e',es' ++ es) ->
                        apps_sem e' (es' ++ es) t =
                        match exprD us vs e ? with
                          | None => None
                          | Some ed => _
                        end.
    Proof.
      induction e; simpl; intros; inv_all; subst; try rewrite apps_sem_nil; auto.
      { unfold app_full in *. simpl in *.
        eapply IHe1 in H.
        unfold apply_sem. simpl.

    Lemma app_fullD : forall e e' es t,
                        app_full e = (e',es) ->
                        exprD us vs e t = apps_sem e' es t.
    Proof.
      induction e; simpl; intros; inv_all; subst; try rewrite apps_sem_nil; auto.
      { unfold app_full in *. simpl in *.
        eapply IHe1 in H.
        unfold apply_sem. simpl.
*)
  End app_sem.

  (** TODO: This is best phrased in terms of monadic logics, but I don't have
   ** access to ILogic due to circular dependency issues
   **)
  Section fold.
    Variable T' : Type.
    Let T := tenv typ -> tenv typ -> T'.
    Variable do_var : var -> T.
    Variable do_uvar : uvar -> T.
    Variable do_inj : sym -> T.
    Variable do_abs : typ -> expr sym -> T -> T.
    Variable do_app : expr sym -> T ->
                      list (expr sym * T) -> T.

    Fixpoint app_fold (e : expr sym) : T :=
      match e with
        | Var v => do_var v
        | UVar u => do_uvar u
        | Inj i => do_inj i
        | Abs t e =>
          @do_abs t e (app_fold e)
        | App l r =>
          (fix gather e (ls : list (expr sym * T)) :=
           match e with
             | App a b =>
               gather a ((b, app_fold b) :: ls)
             | e => do_app e (app_fold e) ls
           end) l ((r,app_fold r) :: nil)
      end.

    Variable R_t : expr sym -> T' -> tenv typ -> tenv typ -> Prop.
    Variable R_s : expr sym -> T' -> env (typD ts) -> env (typD ts) -> Prop.

    Hypothesis Hvar
    : forall tus tvs v,
            R_t (Var v) (do_var v tus tvs) tus tvs
        /\ forall us vs,
             WellTyped_env tus us ->
             WellTyped_env tvs vs ->
             R_s (Var v) (do_var v tus tvs) us vs.
    Hypothesis Huvar
    : forall tus tvs v,
            R_t (UVar v) (do_uvar v tus tvs) tus tvs
        /\ forall us vs,
             WellTyped_env tus us ->
             WellTyped_env tvs vs ->
             R_s (UVar v) (do_uvar v tus tvs) us vs.
    Hypothesis Hinj
    : forall tus tvs v,
            R_t (Inj v) (do_inj v tus tvs) tus tvs
        /\ forall us vs,
             WellTyped_env tus us ->
             WellTyped_env tvs vs ->
             R_s (Inj v) (do_inj v tus tvs) us vs.
    Hypothesis Habs
    : forall tus tvs t e e_res,
        R_t e (e_res tus (t :: tvs)) tus (t :: tvs) ->
           R_t (Abs t e) (do_abs t e e_res tus tvs) tus tvs
        /\ forall us vs,
             WellTyped_env tus us ->
             WellTyped_env tvs vs ->
             (forall x,
                R_s e (e_res tus (t :: tvs)) us (@existT _ _ t x :: vs)) ->
             R_s (Abs t e) (do_abs t e e_res tus tvs) us vs.
    Hypothesis Happ
    : forall tus tvs l l_res rs,
        R_t l (l_res tus tvs) tus tvs ->
        Forall (fun x => R_t (fst x) (snd x tus tvs) tus tvs) rs ->
           R_t (apps l (map fst rs)) (do_app l l_res rs tus tvs) tus tvs
        /\ forall us vs,
             R_s l (l_res tus tvs) us vs ->
             Forall (fun x => R_s (fst x) (snd x tus tvs) us vs) rs ->
             R_s (apps l (map fst rs))
                 (do_app l l_res rs tus tvs)
                 us vs.

    Theorem app_fold_sound
    : forall tus e tvs result,
        app_fold e tus tvs = result ->
           R_t e result tus tvs
        /\ forall us vs,
             WellTyped_env tus us ->
             WellTyped_env tvs vs ->
             R_s e result us vs.
    Proof.
      intro tus.
      refine (expr_strong_ind _ _).
      destruct e; simpl; intros; try solve [ subst; eauto ].
      { assert (Forall (fun x => R_t (fst x) (snd x tus tvs) tus tvs)
                       ((e2, app_fold e2) :: nil)).
        { constructor; [ | constructor ].
          eapply H; eauto with typeclass_instances. }
        assert (forall us vs,
                  WellTyped_env tus us ->
                  WellTyped_env tvs vs ->
                  Forall (fun x => R_s (fst x) (snd x tus tvs) us vs)
                         ((e2, app_fold e2) :: nil)).
        { clear - H1 H. intros.
          constructor; [ | constructor ]; simpl.
          eapply H; eauto with typeclass_instances. }
        cutrewrite (App e1 e2 = apps e1 (map fst ((e2, app_fold e2) :: nil)));
          [ | reflexivity ].
        generalize dependent ((e2, app_fold e2) :: nil).
        assert (forall y : expr sym,
                  SolveTypeClass
                    (TransitiveClosure.rightTrans (expr_acc (func:=sym)) y e1) ->
                  forall (tvs : tenv typ) (result : T'),
                    app_fold y tus tvs = result ->
                    R_t y result tus tvs /\
                    (forall us vs : env (typD ts),
                       WellTyped_env tus us -> WellTyped_env tvs vs -> R_s y result us vs)).
        { clear - H. intros.
          destruct (fun x => H y x _ _ H0).
          { eapply TransitiveClosure.RTStep. eauto. constructor. }
          { intuition. } }
        specialize (H e1 _ tvs).
        revert result. clear - H H0 Happ.
        specialize (@Happ tus tvs).
        induction e1; simpl; intros; subst.
        { specialize (H _ eq_refl); destruct H.
          specialize (@Happ (Var v) (do_var v) l H H2). intuition. }
        { specialize (H _ eq_refl); destruct H.
          specialize (@Happ _ _ l H H2). intuition. }
        {
          change (apps (App e1_1 e1_2) (map fst l))
            with (apps e1_1 (map fst ((e1_2,app_fold e1_2) :: l))).
          specialize (@Happ e1_1 (app_fold e1_1) ((e1_2,app_fold e1_2) :: l)).
          destruct (fun x => IHe1_1 (H0 e1_1 _ tvs) x _ ((e1_2, app_fold e1_2) :: l) eq_refl); clear IHe1_1.
          { intros.
            eapply (H0 y); eauto.
            eapply TransitiveClosure.RTStep. eassumption. constructor. }
          { constructor; eauto. eapply H0; eauto with typeclass_instances. }
          { intros; constructor; eauto. simpl. eapply H0; eauto with typeclass_instances. }
          { split; eauto. } }
        { specialize (H _ eq_refl); destruct H.
          specialize (@Happ _ _ l H H2). intuition. }
        { specialize (H _ eq_refl); destruct H.
          specialize (@Happ _ _ l H H2). intuition. } }
      { specialize (H e _ (t :: tvs) _ eq_refl); destruct H.
        specialize (@Habs tus tvs t e (app_fold e) H); destruct Habs.
        subst; intuition.
        eapply H4; eauto.
        intros. eapply H1; eauto.
        constructor; auto. }
    Qed.

  End fold.

  Record AppFullFoldArgs (T : Type) : Type :=
  { do_var : var -> tenv typ -> tenv typ -> T
  ; do_uvar : uvar -> tenv typ -> tenv typ -> T
  ; do_inj : sym -> tenv typ -> tenv typ -> T
  ; do_abs : typ -> expr sym -> (tenv typ -> tenv typ -> T) ->
             tenv typ -> tenv typ -> T
  ; do_app : expr sym -> (tenv typ -> tenv typ -> T) ->
             list (expr sym * (tenv typ -> tenv typ -> T)) ->
             tenv typ -> tenv typ -> T
  }.

  Definition app_fold_args {T} (Args : AppFullFoldArgs T)
  : expr sym -> tenv typ -> tenv typ -> T :=
    match Args with
      | {| do_var := do_var ; do_uvar := do_uvar ; do_inj := do_inj
         ; do_abs := do_abs ; do_app := do_app |} =>
        @app_fold T do_var do_uvar do_inj do_abs do_app
    end.

  Record AppFullFoldArgsOk {T} (Args : AppFullFoldArgs T) : Type :=
  { R_t : expr sym -> T -> tenv typ -> tenv typ -> Prop
  ; R_s : expr sym -> T -> env (typD ts) -> env (typD ts) -> Prop
  ; Hvar
    : forall tus tvs v,
            R_t (Var v) (Args.(do_var) v tus tvs) tus tvs
        /\ forall us vs,
             WellTyped_env tus us ->
             WellTyped_env tvs vs ->
             R_s (Var v) (Args.(do_var) v tus tvs) us vs
  ; Huvar
    : forall tus tvs v,
            R_t (UVar v) (Args.(do_uvar) v tus tvs) tus tvs
        /\ forall us vs,
             WellTyped_env tus us ->
             WellTyped_env tvs vs ->
             R_s (UVar v) (Args.(do_uvar) v tus tvs) us vs
  ; Hinj
    : forall tus tvs v,
            R_t (Inj v) (Args.(do_inj) v tus tvs) tus tvs
        /\ forall us vs,
             WellTyped_env tus us ->
             WellTyped_env tvs vs ->
             R_s (Inj v) (Args.(do_inj) v tus tvs) us vs
  ; Habs
    : forall tus tvs t e e_res,
        R_t e (e_res tus (t :: tvs)) tus (t :: tvs) ->
           R_t (Abs t e) (Args.(do_abs) t e e_res tus tvs) tus tvs
        /\ forall us vs,
             WellTyped_env tus us ->
             WellTyped_env tvs vs ->
             (forall x,
                R_s e (e_res tus (t :: tvs)) us (@existT _ _ t x :: vs)) ->
             R_s (Abs t e) (Args.(do_abs) t e e_res tus tvs) us vs
  ; Happ
    : forall tus tvs l l_res rs,
        R_t l (l_res tus tvs) tus tvs ->
        Forall (fun x => R_t (fst x) (snd x tus tvs) tus tvs) rs ->
           R_t (apps l (map fst rs)) (Args.(do_app) l l_res rs tus tvs) tus tvs
        /\ forall us vs,
             R_s l (l_res tus tvs) us vs ->
             Forall (fun x => R_s (fst x) (snd x tus tvs) us vs) rs ->
             R_s (apps l (map fst rs))
                 (Args.(do_app) l l_res rs tus tvs)
                 us vs
  }.

  Section sem_fold.
    Variable T : Type.
    Variable Args : AppFullFoldArgs T.

    Variable Rs_t : typ -> T -> tenv typ -> tenv typ -> Prop.
    Variable Rs_s : forall t, typD ts nil t -> T -> 
                              env (typD ts) -> env (typD ts) -> Prop.
    Hypothesis Hvar
    : forall tus tvs v t,
        let result := Args.(do_var) v tus tvs in
        nth_error tvs v = Some t ->
           Rs_t t result tus tvs
        /\ forall (us : hlist _ tus) (vs : hlist _ tvs) val,
             exprD (join_env us) (join_env vs) (Var v) t = Some val ->
             @Rs_s t val result (join_env us) (join_env vs).
    Hypothesis Huvar
    : forall tus tvs v t,
        let result := Args.(do_uvar) v tus tvs in
        nth_error tus v = Some t ->
           Rs_t t result tus tvs
        /\ forall (us : hlist _ tus) (vs : hlist _ tvs) val,
             exprD (join_env us) (join_env vs) (UVar v) t = Some val ->
             @Rs_s t val result (join_env us) (join_env vs).
    Hypothesis Hsym
    : forall tus tvs v t,
        let result := Args.(do_inj) v tus tvs in
        typeof_sym v = Some t ->
           Rs_t t result tus tvs
        /\ forall (us : hlist _ tus) (vs : hlist _ tvs) val,
             exprD (join_env us) (join_env vs) (Inj v) t = Some val ->
             @Rs_s t val result (join_env us) (join_env vs).
    (** INTERESTING ONES **)
    Hypothesis Habs
    : forall tus tvs t e e_res t',
        let result := Args.(do_abs) t e e_res tus tvs in
        typeof_expr tus (t :: tvs) e = Some t' ->
        Rs_t t' (e_res tus (t :: tvs)) tus (t :: tvs) ->
           Rs_t (tyArr t t') result tus tvs
        /\ forall (us : hlist _ tus) (vs : hlist _ tvs) val,
             exprD (join_env us) (join_env vs)
                   (Abs t e) (tyArr t t') = Some val ->
             (forall x,
                @Rs_s t' (val x) (e_res tus (t :: tvs)) (join_env us)
                      ((@existT _ (typD ts nil) t x) :: join_env vs)) ->
             @Rs_s (tyArr t t') val result (join_env us) (join_env vs).

(*
    Hypothesis Happ
    : forall us tvs l l_res (rs : list (expr sym * T)) t
             (tvals : list {t : typ & hlist (typD ts nil) tvs -> typD ts nil t}) val,
        exprD' us tvs l (fold_left (fun x y => tyArr y x) (map (@projT1 _ _) tvals) t) = Some val ->
        Forall2 (fun e tval => exprD' us tvs (fst e) (projT1 tval) = Some (projT2 tval))
                rs
                tvals ->
        forall vs : hlist (typD ts nil) tvs,
          @R (fold_left (fun x y => tyArr y x) (map (@projT1 _ _) tvals) t)
             (val vs) (l_res (typeof_env us) tvs) us (join_env vs) ->
          Forall2 (fun x (t : {t : typ & hlist (typD ts nil) tvs -> typD ts nil t}) =>
                     @R (projT1 t) (projT2 t vs) (snd x (typeof_env us) tvs) us (join_env vs))
                  rs
                  tvals ->
          @R t (apply  vs tvals t (val vs))
             (do_app l l_res rs (typeof_env us) tvs)
             us (join_env vs).
*)


    Definition semArgsOk : AppFullFoldArgsOk Args.
    refine (
        {| R_t := fun e res tus tvs =>
                    match typeof_expr tus tvs e with
                      | Some t => Rs_t t res tus tvs
                      | None => True
                    end
         ; R_s := fun e res us vs =>
                    match typeof_expr (typeof_env us) (typeof_env vs) e with
                      | None => True
                      | Some t =>
                        match exprD us vs e t with
                          | None => False
                          | Some val => @Rs_s t val res us vs
                        end
                    end
        |}).
    { simpl; intros.
      consider (nth_error tvs v); intros.
      { generalize H; eapply Hvar with (tus := tus) in H. intuition.
        apply WellTyped_env_typeof_env in H3. subst.
        rewrite H0.
        red_exprD.
        unfold lookupAs.
        rewrite nth_error_typeof_env in H0. forward.
        inv_all; subst; simpl. red_exprD.
        rewrite typ_cast_typ_refl in *.
        admit. }
      { intuition.
        apply WellTyped_env_typeof_env in H1. subst.
        rewrite H. auto. } }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
(* 
      cutrewrite (vs = join_env (projT2 (split_env vs))).
      { rewrite typeof_env_join_env.
        unfold exprD in H. destruct (split_env vs).
        remember (exprD' us x (Var v) t).
        destruct o.
        { inv_all. subst. simpl.
          eapply Hvar; eauto. }
        { inversion H. } }
      { rewrite join_env_split_env. reflexivity. } }
    { simpl; intros.
      cutrewrite (vs = join_env (projT2 (split_env vs))).
      { rewrite typeof_env_join_env.
        unfold exprD in H. destruct (split_env vs).
        remember (exprD' us x (UVar v) t).
        destruct o.
        { inv_all. subst. simpl.
          eapply Huvar; eauto. }
        { inversion H. } }
      { rewrite join_env_split_env. reflexivity. } }
    { simpl; intros.
      cutrewrite (vs = join_env (projT2 (split_env vs))).
      { rewrite typeof_env_join_env.
        unfold exprD in H. destruct (split_env vs).
        remember (exprD' us x (Inj i) t).
        destruct o.
        { inv_all. subst. simpl.
          eapply Hinj; eauto. }
        { inversion H. } }
      { rewrite join_env_split_env. reflexivity. } }
    { clear - Habs. simpl; intros.
      cutrewrite (vs = join_env (projT2 (split_env vs))).
      { rewrite typeof_env_join_env.
        unfold exprD in H0.
        remember (split_env vs); destruct s.
        red_exprD. destruct t0.
        { inversion H0. }
        { simpl.
          remember (typ_cast_typ ts nil t0_1 t).
          remember (exprD' us (t :: x) e t0_2).
          destruct o.
          2: inversion H0.
          destruct o0.
          2: inversion H0.
          inv_all. subst.
          symmetry in Heqo. inv_all. subst.
          eapply Habs; eauto.
          intros.
          specialize (H x0 t0_2 (t0 (Hcons x0 h))).
          assert (x = typeof_env vs).
          { clear - Heqs. admit. }
          assert (join_env h = vs).
          { clear - Heqs. admit. }
          subst vs.
          replace (t :: x) with (t :: typeof_env (join_env h)).
          { eapply H. unfold exprD.
            simpl. rewrite split_env_join_env; simpl.
            rewrite <- Heqo0. auto. }
          { f_equal. rewrite typeof_env_join_env. auto. } }
        { inversion H0. }
        { inversion H0. } }
      { rewrite join_env_split_env. reflexivity. } }
    { clear - Happ. simpl; intros.
      specialize (@Happ us (typeof_env vs) l l_res rs t).
      revert Happ. revert H1. revert H.
      revert l_res; revert val; revert t; revert l.
      clear - H0. induction H0; simpl; intros.
      { specialize (@Happ nil); simpl in *.
        unfold exprD in *.
        remember (split_env vs); destruct s.
        remember (exprD' us x l t); destruct o.
        2: inversion H1.
        inv_all; subst.
        assert (x = typeof_env vs).
        { admit. }
        subst. specialize (H t). rewrite <- Heqo in *.
        specialize (fun x => @Happ _ eq_refl (Forall2_nil _) h x (Forall2_nil _)).
        specialize (@H _ eq_refl).
        cutrewrite (join_env h = vs) in Happ. auto.
        rewrite <- split_env_projT2_join_env with (vs := vs); auto. }
      { rewrite exprD_apps in H2.
        unfold apps_sem in H2.
        simpl in H2.
        consider (typeof_expr (typeof_env us) (typeof_env vs) l0).
        { intros.
          consider (typeof_expr (typeof_env us) (typeof_env vs) (fst x)).
          { intros. destruct t0; simpl in H4; try solve [ inversion H4 ].
            consider (typ_eqb t0_1 t1); intros. subst.
            { consider (exprD us vs (App l0 (fst x)) t0_2).
              { (* intros.
                red_exprD. rewrite H2 in H4.
                consider (exprD us vs l0 (tyArr t1 t0_2)); try solve [ inversion 2 ]; intros.
                consider (exprD us vs (fst x) t1); try solve [ inversion 2 ]; intros.
                rewrite typ_cast_typ_refl in *. inv_all. subst.
                unfold exprD in *.
                consider (split_env vs); intros.
                consider (exprD' us x0 l0 (tyArr t1 t0_2)); try solve [ inversion 2 ]; intros.
                consider (exprD' us x0 (fst x) t1); try solve [ inversion 2 ]; intros.
                inv_all; subst.
                replace vs with (join_env (projT2 (split_env vs))).
                rewrite typeof_env_join_env.
                Lemma projT1_split_env_typeof_env
                : forall vs,
                    projT1 (split_env (typD := typD ts) vs) = typeof_env vs.
                Proof.
                Admitted.
                replace (do_app l0 l_res (x :: l) (typeof_env us) (projT1 (split_env vs)))
                   with (do_app l0 l_res (x :: l) (typeof_env us) (typeof_env vs)).
                { rewrite H. simpl. admit. 
                  cutrewrite (val = apply h _ t (t4 h)).
eapply Happ.

                cut (R t val (do_app l0 l_res (x :: l) (typeof_env us) (typeof_env vs))
                          us (join_env (projT2 (split_env vs)))).
                { rewrite projT1_split_env_typeof_env at 1.

                replace (projT1 (split_env 
                
                                            
                } *) admit.
                
              }
              { inversion 2. } }
            { inversion H5. } }
          { inversion 2. } }
        { inversion 2. } } }
*)
    Qed.
  End sem_fold.

End app_full.
