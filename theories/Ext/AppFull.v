Require Import Coq.Arith.Compare_dec.
Require Import ExtLib.Data.Pair.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SymI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
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

  Section apps_type.
    Variables tus tvs : tenv typ.

    Fixpoint type_of_applys (t : typ) (es : list (expr sym)) {struct es} : option typ :=
      match es with
        | nil => Some t
        | e :: es =>
          match typeof_expr tus tvs e , t with
            | Some t' , tyArr td tr =>
              match typ_cast_typ ts nil t' td with
                | Some _ => type_of_applys tr es
                | _ => None
              end
            | _ , _ => None
          end
      end.

    Definition typeof_apps (e : expr sym) (es : list (expr sym)) : option typ :=
      match typeof_expr tus tvs e with
        | Some t => type_of_applys t es
        | None => None
      end.

    Lemma type_of_applys_typeof_None
    : forall es e,
        typeof_expr tus tvs e = None ->
        typeof_expr tus tvs (apps e es) = None.
    Proof.
      induction es; simpl; intros; auto.
      rewrite IHes; auto.
      simpl. rewrite H. auto.
    Qed.

    Lemma type_of_applys_typeof
    : forall es e t,
        typeof_expr tus tvs e = Some t ->
        typeof_expr tus tvs (apps e es) = type_of_applys t es.
    Proof.
      induction es; simpl; intros; auto.
      { consider (typeof_expr tus tvs a); intros.
        { destruct t; simpl;
          try solve [
                rewrite type_of_applys_typeof_None;
                simpl; Cases.rewrite_all; auto ].
          match goal with
            | |- context [ match ?X with _ => _ end ] =>
              consider X; intros
          end.
          inv_all. subst.
          { erewrite IHes. reflexivity.
            simpl; Cases.rewrite_all; simpl.
            consider (typ_eqb t1 t1); try reflexivity.
            congruence. }
          { rewrite type_of_applys_typeof_None; auto.
            simpl. Cases.rewrite_all. simpl.
            consider (typ_eqb t1 t0); auto; intros.
            subst. rewrite typ_cast_typ_refl in H1.
            congruence. } }
        { rewrite type_of_applys_typeof_None; auto.
          simpl. rewrite H. rewrite H0. auto. } }
    Qed.

    Theorem typeof_expr_apps
    : forall e es,
        typeof_expr tus tvs (apps e es) = typeof_apps e es.
    Proof.
      intros. unfold typeof_apps.
      consider (typeof_expr tus tvs e); intros.
      { eapply type_of_applys_typeof; auto. }
      { rewrite type_of_applys_typeof_None; auto. }
    Qed.

  End apps_type.

  Theorem tyArr_circ_L : forall a b, a = tyArr a b -> False.
  Proof.
    clear.
    induction a; intros; try congruence.
  Qed.
  Theorem tyArr_circ_R : forall a b, a = tyArr b a -> False.
  Proof.
    clear.
    induction a; intros; try congruence.
  Qed.

  Fixpoint typ_size (t : typ) : nat :=
    match t with
      | tyProp => 1
      | tyType _ => 1
      | tyArr a b => typ_size a + typ_size b + 1
      | tyVar _ => 1
    end.

  Lemma type_of_applys_circle_False_lem
  : forall tus tvs ls t t',
      type_of_applys tus tvs t ls = Some t' ->
      typ_size t >= typ_size t'.
  Proof.
    clear.
    induction ls; intros.
    { simpl in *. inv_all. subst.
      omega. }
    { simpl in *. forward. subst.
      inv_all. subst.
      eapply IHls in H2. simpl. omega. }
  Qed.

  Lemma type_of_applys_circle_False
  : forall tus tvs ls t t',
      type_of_applys tus tvs t ls = Some (tyArr t' t) -> False.
  Proof.
    clear.
    intros. eapply type_of_applys_circle_False_lem in H.
    simpl in *. omega.
  Qed.

  Section app_sem.
    Variables us vs : env (typD ts).

    Fixpoint apply {T} (x : T) (ls : list {t : typ & T -> typD ts nil t}) t {struct ls} :
      typD ts nil (fold_right tyArr t (map (@projT1 _ _) ls)) ->
      typD ts nil t :=
      match ls as ls
            return typD ts nil (fold_right tyArr t (map (@projT1 _ _) ls)) ->
                   typD ts nil t
      with
        | nil => fun x => x
        | l :: ls => fun f => apply x ls _ (f (projT2 l x))
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
        destruct H.
        rewrite H.
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

  End app_sem.


  Section app_sem'.
    Variables us vs : tenv typ.

(*
    Fixpoint apply' {T U} (x : T) (y : U) (ls : list {t : typ & T -> U -> typD ts nil t}) t {struct ls} :
      typD ts nil (fold_right tyArr t (map (@projT1 _ _) ls)) ->
      T -> U -> typD ts nil t :=
      match ls as ls
            return typD ts nil (fold_right tyArr t (map (@projT1 _ _) ls)) ->
                   typD ts nil t
      with
        | nil => fun x => x
        | l :: ls => fun f => apply x ls _ (f (projT2 l x))
      end.
*)

    Fixpoint apply_sem'
             (tf : typ) (e : hlist (typD ts nil) us -> hlist (typD ts nil) vs -> typD ts nil tf)
             (ls : list (expr sym)) (t : typ)
             {struct ls}
    : option (hlist (typD ts nil) us -> hlist (typD ts nil) vs -> typD ts nil t) :=
      match ls with
        | nil =>
          match typ_cast_typ ts nil tf t with
            | None => None
            | Some cast => Some (cast (fun x => hlist (typD ts nil) us -> hlist (typD ts nil) vs -> x) e)
          end
        | l :: ls =>
          match tf as tf
                return (hlist (typD ts nil) us -> hlist (typD ts nil) vs -> typD ts nil tf) -> _
          with
            | tyArr a b => fun f =>
                             match exprD' us vs l a with
                               | None => None
                               | Some x => apply_sem' b (fun u g => (f u g) (x u g)) ls t
                             end
            | _ => fun _ => None
          end e
      end.

    Definition apps_sem'
               (e : expr sym) (l : list (expr sym)) (t : typ)
    : option (hlist (typD ts nil) us -> hlist (typD ts nil) vs -> typD ts nil t) :=
      match typeof_expr us vs e with
        | None => None
        | Some tf =>
          match exprD' us vs e tf with
            | Some f => apply_sem' _ f l t
            | None => None
          end
      end.

    Lemma apps_sem'_nil : forall e t,
                           apps_sem' e nil t = exprD' us vs e t.
    Proof.
      intros. unfold apps_sem'.
      consider (typeof_expr us vs e); intros.
      { eapply typeof_expr_exprD' in H.
        destruct H.
        rewrite H.
        simpl.
        match goal with
          | |- match ?X with _ => _ end = _ =>
            consider X; intros
        end.
        { inv_all. subst. auto. }
        { rewrite exprD'_type_cast in *.
          forward. inv_all.
          revert H3. subst. subst; intros.
          autorewrite with exprD_rw in *. congruence. } }
      { consider (exprD' us vs e t); auto; intros.
        exfalso.
        assert (exists v, exprD' us vs e t = Some v); eauto.
        eapply typeof_expr_exprD' in H1. red in H1.
        congruence. }
    Qed.

    Lemma exprD'_apps : forall es e t,
      exprD' us vs (apps e es) t = apps_sem' e es t.
    Proof.
      induction es; simpl; intros.
      { unfold apps_sem'.
        rewrite exprD'_type_cast. forward. simpl.
        match goal with
          | |- match ?X with _ => _ end = match _ with Some f => match ?Y with _ => _ end | None => _ end =>
            change Y with X; consider X
        end; intros; forward.
        inv_all. subst. reflexivity. }
      { rewrite IHes.
        unfold apps_sem'.
        simpl. forward.
        consider (typeof_expr us vs a); intros.
        { destruct t0; forward.
          simpl.
          consider (typ_eqb t0_1 t1); intros; subst.
          { red_exprD. Cases.rewrite_all.
            forward. rewrite typ_cast_typ_refl. reflexivity. }
          { forward. exfalso.
            rewrite exprD'_type_cast in H3.
            rewrite H0 in *.
            rewrite typ_cast_typ_neq in * by auto.
            congruence. } }
        { forward. subst.
          rewrite exprD'_type_cast in H3. rewrite H0 in *. congruence. } }
    Qed.

  End app_sem'.

  (** TODO: This is best phrased in terms of monadic logics, but I don't have
   ** access to ILogic due to circular dependency issues
   **)
  Section fold.
    Variable T' : Type.
    Let T : Type := tenv typ -> tenv typ -> T'.
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

    Variable R_t : typ -> expr sym -> T' -> tenv typ -> tenv typ -> Prop.

    Hypothesis Hvar
    : forall tus tvs v t,
        typeof_expr tus tvs (Var v) = Some t ->
        R_t t (Var v) (do_var v tus tvs) tus tvs.
    Hypothesis Huvar
    : forall tus tvs v t,
        typeof_expr tus tvs (UVar v) = Some t ->
        R_t t (UVar v) (do_uvar v tus tvs) tus tvs.
    Hypothesis Hinj
    : forall tus tvs v t,
        typeof_expr tus tvs (Inj v) = Some t ->
        R_t t (Inj v) (do_inj v tus tvs) tus tvs.
    Hypothesis Habs
    : forall tus tvs t t' e e_res,
        typeof_expr tus tvs (Abs t e) = Some (tyArr t t') ->
        R_t t' e (e_res tus (t :: tvs)) tus (t :: tvs) ->
        R_t (tyArr t t') (Abs t e) (do_abs t e e_res tus tvs) tus tvs.
    Hypothesis Happ
    : forall tus tvs l l_res rs t ts,
        typeof_expr tus tvs (apps l (map fst rs)) = Some t ->
        let ft := fold_right tyArr t ts in
        R_t ft l (l_res tus tvs) tus tvs ->
        Forall2 (fun t x =>
                      typeof_expr tus tvs (fst x) = Some t
                   /\ R_t t (fst x) (snd x tus tvs) tus tvs)
                ts rs ->
        R_t t (apps l (map fst rs)) (do_app l l_res rs tus tvs) tus tvs.

    Theorem app_fold_sound
    : forall e tus tvs t result,
        app_fold e tus tvs = result ->
        typeof_expr tus tvs e = Some t ->
        R_t t e result tus tvs.
    Proof.
      refine (expr_strong_ind _ _).
      destruct e; simpl; intros; subst; eauto.
      { repeat match goal with
                 | H : _ |- _ =>
                   solve [ inversion H ]
                 | _ : match ?X with _ => _ end = _ |- _ =>
                   consider X; intros
               end.
        destruct t0; simpl in H2; try solve [ inversion H2 ].
        forward; inv_all; subst.
        assert (Forall2 (fun t x =>
                              typeof_expr tus tvs (fst x) = Some t
                           /\ R_t t (fst x) (snd x tus tvs) tus tvs)
                        (t1 :: nil)
                        ((e2, app_fold e2) :: nil)).
        { constructor; [ simpl | constructor ].
          split; auto.
          eapply H; eauto with typeclass_instances. }
        generalize (H e1 _ tus tvs _ _ eq_refl H0).
        assert (forall y : expr sym,
                  SolveTypeClass
                    (TransitiveClosure.rightTrans (expr_acc (func:=sym)) y e1) ->
                  forall (tus tvs : tenv typ) (t : typ) (result : T'),
                    app_fold y tus tvs = result ->
                    typeof_expr tus tvs y = Some t ->
                    R_t t y result tus tvs).
        { clear - H. intuition.
          eapply H; eauto.
          eapply TransitiveClosure.RTStep. eauto. constructor. }
        assert (typeof_expr tus tvs (apps e1 (map fst ((e2, app_fold e2) :: nil))) = Some t).
        { simpl. rewrite H0. rewrite H1. simpl. forward. }
        revert H2 H0 H3 H4.
        change (App e1 e2)
          with (apps e1 (map fst ((e2, app_fold e2) :: nil))).
        change (tyArr t1 t)
          with (fold_right tyArr t (t1 :: nil)).
        generalize ((e2, app_fold e2) :: nil).
        generalize (t1 :: nil).
        clear - Happ. specialize (@Happ tus tvs).
        Opaque app_fold.
        induction e1; simpl; intros; eauto.
        { repeat match goal with
                   | H : _ |- _ =>
                     solve [ inversion H ]
                   | _ : match ?X with _ => _ end = _ |- _ =>
                     consider X; intros
                 end.
          destruct t0; simpl in *; try solve [ inversion H5 ].
          forward; inv_all; subst.
          change (apps (App e1_1 e1_2) (map fst l0))
            with (apps e1_1 (map fst ((e1_2,app_fold e1_2) :: l0))).
          eapply IHe1_1; eauto.
          { constructor; eauto.
            simpl. split; eauto.
            eapply H3. simpl; eauto with typeclass_instances.
            reflexivity. simpl. eauto. }
          { reflexivity. }
          { intros.
            eapply H3; eauto.
            eapply TransitiveClosure.RTStep. eauto. constructor. }
          { eapply H3; eauto with typeclass_instances. } }
        Transparent app_fold. }
      { forward; inv_all; subst.
        specialize (H e _ tus (t :: tvs) _ _ eq_refl H0).
        eapply Habs; eauto. simpl. rewrite H0. auto. }
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

  Record AppFullFoldArgsOk {T} (Args : AppFullFoldArgs T)
         (R_t : typ -> expr sym -> T -> tenv typ -> tenv typ -> Prop) : Type :=
  { Hvar
    : forall tus tvs v t,
        typeof_expr tus tvs (Var v) = Some t ->
        R_t t (Var v) (Args.(do_var) v tus tvs) tus tvs
  ; Huvar
    : forall tus tvs v t,
        typeof_expr tus tvs (UVar v) = Some t ->
        R_t t (UVar v) (Args.(do_uvar) v tus tvs) tus tvs
  ; Hinj
    : forall tus tvs v t,
        typeof_expr tus tvs (Inj v) = Some t ->
        R_t t (Inj v) (Args.(do_inj) v tus tvs) tus tvs
  ; Habs
    : forall tus tvs t t' e e_res,
        typeof_expr tus tvs (Abs t e) = Some (tyArr t t') ->
        R_t t' e (e_res tus (t :: tvs)) tus (t :: tvs) ->
        R_t (tyArr t t') (Abs t e) (Args.(do_abs) t e e_res tus tvs) tus tvs
  ; Happ
    : forall tus tvs l l_res rs t ts,
        typeof_expr tus tvs (apps l (map fst rs)) = Some t ->
        let ft := fold_right tyArr t ts in
        R_t ft l (l_res tus tvs) tus tvs ->
        Forall2 (fun t x =>
                      typeof_expr tus tvs (fst x) = Some t
                   /\ R_t t (fst x) (snd x tus tvs) tus tvs)
                ts
                rs ->
        R_t t (apps l (map fst rs)) (Args.(do_app) l l_res rs tus tvs) tus tvs
  }.

  Theorem app_fold_args_sound {T} (args : AppFullFoldArgs T)
          R_t
          (sound : AppFullFoldArgsOk args R_t)
  : forall e tus tvs t result,
      app_fold_args args e tus tvs = result ->
      typeof_expr tus tvs e = Some t ->
      R_t t e result tus tvs.
  Proof.
    intros.
    unfold app_fold_args in *. destruct args.
    eapply app_fold_sound with (R_t := R_t) in H; try eassumption.
    eapply (Hvar sound).
    eapply (Huvar sound).
    eapply (Hinj sound).
    eapply (Habs sound).
    eapply (Happ sound).
  Qed.

  Section wf_fold.
    Variable T' : expr sym -> Type.
    Let T (e : expr sym) : Type := tenv typ -> tenv typ -> T' e.
    Variable do_var : forall v, T (Var v).
    Variable do_uvar : forall u, T (UVar u).
    Variable do_inj : forall i, T (Inj i).
    Variable do_abs : forall (rt : expr sym -> Type)
                             (srt : forall e e', expr_acc e' e -> rt e -> rt e')
                             (recur : forall e, rt e -> T e)
                             (t : typ) e (r : rt e), T (Abs t e).
    Variable do_app : forall (rt : expr sym -> Type)
                             (srt : forall e e', expr_acc e' e -> rt e -> rt e')
                             (recur : forall e, rt e -> T e)
                             e es (r : rt e) (ls : hlist rt es), T (apps e es).

    Require Import ExtLib.Recur.GenRec.
    Require Import ExtLib.Recur.Relation.

    Let acc := TransitiveClosure.leftTrans (expr_acc (func:=sym)).

    Definition wf_para : forall e, T e :=
      @Fix (expr sym) acc (wf_leftTrans (@wf_expr_acc sym))
           T
           (fun e =>
              match e as e
                    return (forall y, acc y e -> T y) -> T e
              with
                | Var v => fun _ => do_var v
                | UVar u => fun _ => do_uvar u
                | Inj s => fun _ => do_inj s
                | Abs t e => fun rec =>
                  @do_abs (fun x => acc x (Abs t e))
                          (fun _ _ pf pf' =>
                             TransitiveClosure.LTStep _ pf pf')
                          rec t e
                          (TransitiveClosure.LTFin _ _ _ (acc_Abs _ _))
                | App f es => fun rec =>
                  (fix gather e' ls
                   : forall (etkn : acc e' (App f es))
                            (tkns : hlist (fun x => acc x (App f es)) ls),
                       T (apps e' ls) :=
                     match e' as e'
                           return forall (etkn : acc e' (App f es))
                                         (tkns : hlist (fun x => acc x (App f es)) ls),
                                    T (apps e' ls)
                     with
                       | App a b => fun etkn tkns =>
                         gather a (b :: ls)
                                (TransitiveClosure.LTStep a (acc_App_l a b) etkn)
                                (Hcons
                                   (TransitiveClosure.LTStep b (acc_App_r a b) etkn)
                                   tkns)
                       | z => fun etkn tkns =>
                         @do_app (fun x => acc x (App f es))
                                 (fun _ _ pf pf' =>
                                    TransitiveClosure.LTStep _ pf pf')
                                 rec z ls
                                 etkn tkns
                     end) f (es :: nil)
                          (TransitiveClosure.LTFin _ _ _ (acc_App_l _ _))
                          (Hcons (TransitiveClosure.LTFin _ _ _ (acc_App_r _ _))
                                 Hnil)
              end).
    End wf_fold.

(*
  Section para.
    Variable T' : expr sym -> Type.
    Let T (e : expr sym) : Type := tenv typ -> tenv typ -> T' e.
    Variable do_var : forall v : var, T (Var v).
    Variable do_uvar : forall u : uvar, T (UVar u).
    Variable do_inj : forall i : sym, T (Inj i).
    Variable do_abs : forall (r : Type)
                             (get : r -> expr sym)
                             (recur : forall t : r, T (get t)),
                        forall (t : typ) (r : r), T (Abs t (get r)).
    Variable do_app : forall (rt : Type)
                             (get : rt -> expr sym)
                             (recur : forall r : rt, T (get r)),
                        forall (f : rt) (args : list rt),
                          T (apps (get f) (map get args)).

    Fixpoint app_fold (e : expr sym) : T e.
    refine (
        match e as e return T e with
          | Var v => do_var v
          | UVar u => do_uvar u
          | Inj s => do_inj s
          | Abs t e =>
          | _ => _
        end).

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

    Variable R_t : typ -> expr sym -> T' -> tenv typ -> tenv typ -> Prop.

    Hypothesis Hvar
    : forall tus tvs v t,
        typeof_expr tus tvs (Var v) = Some t ->
        R_t t (Var v) (do_var v tus tvs) tus tvs.
    Hypothesis Huvar
    : forall tus tvs v t,
        typeof_expr tus tvs (UVar v) = Some t ->
        R_t t (UVar v) (do_uvar v tus tvs) tus tvs.
    Hypothesis Hinj
    : forall tus tvs v t,
        typeof_expr tus tvs (Inj v) = Some t ->
        R_t t (Inj v) (do_inj v tus tvs) tus tvs.
    Hypothesis Habs
    : forall tus tvs t t' e e_res,
        typeof_expr tus tvs (Abs t e) = Some (tyArr t t') ->
        R_t t' e (e_res tus (t :: tvs)) tus (t :: tvs) ->
        R_t (tyArr t t') (Abs t e) (do_abs t e e_res tus tvs) tus tvs.
    Hypothesis Happ
    : forall tus tvs l l_res rs t ts,
        typeof_expr tus tvs (apps l (map fst rs)) = Some t ->
        let ft := fold_right tyArr t ts in
        R_t ft l (l_res tus tvs) tus tvs ->
        Forall2 (fun t x => R_t t (fst x) (snd x tus tvs) tus tvs)
                ts rs ->
        R_t t (apps l (map fst rs)) (do_app l l_res rs tus tvs) tus tvs.
*)

End app_full.
