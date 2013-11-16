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

  Fixpoint app_full' (e : expr sym) (acc : list (expr sym)) : expr sym * list (expr sym) :=
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

(*
  Lemma app_fullD : forall us vs e e' es t val,
                      app_full e = (e',es) ->
                      exprD us vs e t = Some val ->
                      exists ts,
*)

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

    Variable R : expr sym -> T' -> env (typD ts) -> env (typD ts) -> Prop.
    Hypothesis Hvar : forall us vs v,
                        R (Var v) (do_var v (typeof_env us) (typeof_env vs)) us vs.
    Hypothesis Huvar : forall us vs v,
                         R (UVar v) (do_uvar v (typeof_env us) (typeof_env vs)) us vs.
    Hypothesis Hinj : forall us vs i,
                        R (Inj i) (do_inj i (typeof_env us) (typeof_env vs)) us vs.
    Hypothesis Habs : forall us vs t e e_res,
                        (forall x, R e (e_res (typeof_env us) (t :: typeof_env vs))
                                     us
                                     (@existT _ _ t x :: vs)) ->
                        R (Abs t e)
                          (do_abs t e e_res (typeof_env us) (typeof_env vs))
                          us vs.
    Hypothesis Happ : forall us vs l l_res rs,
                        R l (l_res (typeof_env us) (typeof_env vs)) us vs ->
                        Forall (fun x => R (fst x) (snd x (typeof_env us) (typeof_env vs)) us vs) rs ->
                        R (apps l (map fst rs))
                          (do_app l l_res rs (typeof_env us) (typeof_env vs))
                          us vs.

    Theorem app_fold_sound : forall us e vs result,
                               app_fold e (typeof_env us) (typeof_env vs) = result ->
                               R e result us vs.
    Proof.
      intro us.
      refine (expr_strong_ind _ _).
      destruct e; simpl; intros; try solve [ subst; eauto ].
      { assert (Forall (fun x => R (fst x) (snd x (typeof_env us) (typeof_env vs)) us vs)
                       ((e2, app_fold e2) :: nil)).
        { repeat constructor; simpl. eapply H; eauto with typeclass_instances. }
        cutrewrite (App e1 e2 = apps e1 (map fst ((e2, app_fold e2) :: nil)));
          [ | reflexivity ].
        generalize dependent ((e2, app_fold e2) :: nil).
        assert (forall y : expr sym, forall vs,
                  SolveTypeClass
                    (TransitiveClosure.rightTrans (expr_acc (func:=sym)) y e1) ->
                  forall result : T, app_fold y = result -> R y (result (typeof_env us) (typeof_env vs)) us vs).
        { clear - H. intuition.
          eapply H; eauto.
          eapply TransitiveClosure.RTStep. eapply X.
          constructor. subst; auto. }
        revert H0. revert result. revert vs. clear H.
        induction e1; simpl; intros; subst; eauto using Happ with typeclass_instances.
        { change (apps (App e1_1 e1_2) (map fst l))
            with (apps e1_1 (map fst ((e1_2,app_fold e1_2) :: l))).
          eapply IHe1_1; eauto.
          { clear - H0.
            intros. subst. eapply H0; eauto.
            red. eapply TransitiveClosure.RTStep. eassumption.
            constructor. }
          { constructor; eauto. simpl.
            eapply H0; eauto with typeclass_instances. } }
        { eapply Happ; eauto.
          eapply Habs. intros. 
          specialize (H0 e1 (@existT _ _ t x :: vs) _ _ eq_refl). eauto. } }
      { subst. eapply Habs. intros; eapply H; eauto with typeclass_instances. }
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

  Record AppFullFoldArgsOk {T} (Args : AppFullFoldArgs T) : Type :=
  { TR : expr sym -> T -> env (typD ts) -> env (typD ts) -> Prop
  ; Hvar : forall us vs v,
              TR (Var v) (Args.(do_var) v (typeof_env us) (typeof_env vs)) us vs
  ; Huvar : forall us vs v,
               TR (UVar v) (Args.(do_uvar) v (typeof_env us) (typeof_env vs)) us vs
  ; Hinj : forall us vs i,
             TR (Inj i) (Args.(do_inj) i (typeof_env us) (typeof_env vs)) us vs
  ; Habs : forall us vs t e e_res,
              (forall x, TR e (e_res (typeof_env us) (t :: typeof_env vs))
                           us
                           (@existT _ _ t x :: vs)) ->
              TR (Abs t e)
                (Args.(do_abs) t e e_res (typeof_env us) (typeof_env vs))
                us vs
  ; Happ : forall us vs l l_res rs,
             TR l (l_res (typeof_env us) (typeof_env vs)) us vs ->
             Forall (fun x => TR (fst x) (snd x (typeof_env us) (typeof_env vs)) us vs) rs ->
             TR (apps l (map fst rs))
               (Args.(do_app) l l_res rs (typeof_env us) (typeof_env vs))
               us vs
  }.

  Section sem_fold.
    Variable TT : Type.
    Let T := tenv typ -> tenv typ -> TT.

    Variable do_var : var -> T.
    Variable do_uvar : uvar -> T.
    Variable do_inj : sym -> T.
    Variable do_abs : typ -> expr sym -> T -> T.
    Variable do_app : expr sym -> T ->
                      list (expr sym * T) -> T.

    Definition semArgs : AppFullFoldArgs TT :=
      @Build_AppFullFoldArgs TT do_var do_uvar do_inj do_abs do_app.

    Variable R : forall t, typD ts nil t -> TT -> env (typD ts) -> env (typD ts) -> Prop.
    Hypothesis Hvar : forall us tvs t v val,
                        exprD' us tvs (Var v) t = Some val ->
                        forall vs,
                          R t (val vs) (do_var v (typeof_env us) tvs) us (join_env vs).
    Hypothesis Huvar : forall us tvs t v val,
                        exprD' us tvs (UVar v) t = Some val ->
                        forall vs,
                          R t (val vs) (do_uvar v (typeof_env us) tvs) us (join_env vs).
    Hypothesis Hinj : forall us tvs t v val,
                        exprD' us tvs (Inj v) t = Some val ->
                        forall vs,
                          R t (val vs) (do_inj v (typeof_env us) tvs) us (join_env vs).
    (** INTERESTING ONES **)
    Hypothesis Habs : forall us tvs t t' e e_res val,
                        exprD' us (t :: tvs) e t' = Some val ->
                        forall (vs : hlist (typD ts nil) tvs),
                          (forall x,
                             R t' (val (Hcons x vs)) (e_res (typeof_env us) (t :: tvs))
                               us ((@existT _ (typD ts nil) t x) :: join_env vs)) ->
                          R (tyArr t t') (fun x => val (Hcons x vs))
                            (do_abs t e e_res (typeof_env us) tvs) us (join_env vs).
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

    Definition semArgsOk : AppFullFoldArgsOk semArgs.
    refine (
        {| TR := fun e res us vs =>
                   forall t val,
                     exprD us vs e t = Some val ->
                     @R t val res us vs |}
          ).
    { simpl; intros. 
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
      { admit. } }
    Qed.
  End sem_fold.

End app_full.
