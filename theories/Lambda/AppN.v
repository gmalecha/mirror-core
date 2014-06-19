Require Import Coq.Arith.Compare_dec.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.Pair.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SymI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprTac.

Set Implicit Arguments.
Set Strict Implicit.

Section app_full.
  Variable typ : Type.
  Variable sym : Type.

  Fixpoint apps (e : expr typ sym) (ls : list (expr typ sym)) :=
    match ls with
      | nil => e
      | l :: ls => apps (App e l) ls
    end.

  Fixpoint app_full' (e : expr typ sym) (acc : list (expr typ sym))
  : expr typ sym * list (expr typ sym) :=
    match e with
      | App l r =>
        app_full' l (r :: acc)
      | _ =>
        (e, acc)
    end.

  Definition app_full (e : expr typ sym) := app_full' e nil.

  Lemma apps_app_full'
  : forall e e' ls ls',
      app_full' e ls = (e', ls') ->
      apps e ls = apps e' ls'.
  Proof.
    induction e; simpl; intros; inv_all; subst; auto.
    eapply IHe1 in H. auto.
  Qed.
End app_full.

Section app_full_proofs.
  Variable typ : Type.
  Variable sym : Type.
  Variable RType_typ : RType typ.
  Variable Typ2_Fun : Typ2 _ Fun.
  Variable RSym_sym : RSym sym.

  Variable RTypeOk : RTypeOk.
  Variable Typ2Ok_Fun : Typ2Ok _.
  Variable RSymOk_sym : RSymOk _.

  Section apps_type.
    Variable ts : list Type.
    Variables tus tvs : tenv typ.

    Fixpoint type_of_applys (t : typ) (es : list (expr typ sym)) {struct es} : option typ :=
      match es with
        | nil => Some t
        | e :: es =>
          match typeof_expr ts tus tvs e with
            | Some t' =>
              typ2_match (fun _ => option _) ts t
                         (fun td tr =>
                            match type_cast ts t' td with
                              | Some _ => type_of_applys tr es
                              | _ => None
                            end)
                         None
            | _ => None
          end
      end.

    Definition typeof_apps (e : expr typ sym)
               (es : list (expr typ sym)) : option typ :=
      match typeof_expr ts tus tvs e with
        | Some t => type_of_applys t es
        | None => None
      end.

    Lemma type_of_applys_typeof_None
    : forall es e,
        typeof_expr ts tus tvs e = None ->
        typeof_expr ts tus tvs (apps e es) = None.
    Proof.
      induction es; simpl; intros; auto.
      rewrite IHes; auto.
      simpl. rewrite H. auto.
    Qed.

    Lemma type_of_applys_typeof
    : forall es e t,
        typeof_expr ts tus tvs e = Some t ->
        typeof_expr ts tus tvs (apps e es) = type_of_applys t es.
    Proof.
      induction es; simpl; intros; auto.
      { consider (typeof_expr ts tus tvs a); intros.
        { arrow_case ts t.
          { rewrite Relim_const in *.
            consider (type_cast ts t0 x); intros.
            { erewrite IHes with (t := x0).
              { rewrite eq_Const_eq. reflexivity. }
              { simpl. rewrite H. rewrite H0.
                unfold type_of_apply. rewrite H1.
                rewrite Relim_const. rewrite eq_Const_eq.
                erewrite type_cast_sym_Some; eauto. } }
          { rewrite type_of_applys_typeof_None.
            rewrite eq_Const_eq; reflexivity.
            simpl. rewrite H0. rewrite H.

            unfold type_of_apply. red in x1. subst.
            rewrite typ2_match_zeta; eauto.
            rewrite type_cast_sym_None; eauto.
            rewrite eq_Const_eq. reflexivity. } }
          { rewrite type_of_applys_typeof_None; auto.
            simpl. Cases.rewrite_all_goal.
            unfold type_of_apply.
            rewrite H1. reflexivity. } }
        { rewrite type_of_applys_typeof_None; auto.
          simpl. Cases.rewrite_all_goal.
          unfold type_of_apply. reflexivity. } }
    Qed.

    Theorem typeof_expr_apps
    : forall e es,
        typeof_expr ts tus tvs (apps e es) = typeof_apps e es.
    Proof.
      intros. unfold typeof_apps.
      consider (typeof_expr ts tus tvs e); intros.
      { eapply type_of_applys_typeof; auto. }
      { rewrite type_of_applys_typeof_None; auto. }
    Qed.

  End apps_type.

  Theorem tyArr_circ_L : forall a b, a = typ2 a b -> False.
  Proof.
    refine ((@Fix _ _ (@wf_tyAcc _ _ _)
                  (fun x => forall b, x = typ2 x b -> False)
                  (fun a rec b pf =>
                     rec a match eq_sym pf in (_ = t) return (tyAcc a t) with
                             | eq_refl => tyAcc_typ2L a b
                           end b pf))).
  Qed.
  Theorem tyArr_circ_R : forall a b, a = typ2 b a -> False.
  Proof.
    refine ((@Fix _ _ (@wf_tyAcc _ _ _)
                  (fun x => forall b, x = typ2 b x -> False)
                  (fun a rec b pf =>
                     rec a match eq_sym pf in (_ = t) return (tyAcc a t) with
                             | eq_refl => tyAcc_typ2R a b
                           end b pf))).
  Qed.

  Require Import ExtLib.Relations.TransitiveClosure.
  Require Import ExtLib.Recur.Facts.

  Lemma type_of_applys_circle_False_lem
  : forall ts tus tvs ls t t',
      type_of_applys ts tus tvs t ls = Some t' ->
      leftTrans (@tyAcc _ _) t t' ->
      False.
  Proof.
    induction ls; simpl in *; intros.
    { inv_all. subst.
      eapply (@irreflexivity _ _ (@wf_anti_sym _ _ (Relation.wf_leftTrans (@wf_tyAcc _ _ _)))) in H0.
      assumption. }
    { forward. arrow_case ts t.
      { rewrite Relim_const in *.
        rewrite eq_Const_eq in *. forward.
        clear H2. destruct r. symmetry in x1. destruct x1.
        eapply IHls in H3. auto.
        eapply LTStep. 2: eapply H0.
        eapply tyAcc_typ2R; eauto. }
      { congruence. } }
  Qed.

  Lemma type_of_applys_circle_False
  : forall ts tus tvs ls t t',
      type_of_applys ts tus tvs t ls = Some (typ2 t' t) -> False.
  Proof.
    intros. eapply type_of_applys_circle_False_lem.
    eassumption. constructor. eapply tyAcc_typ2R; eauto.
  Qed.

  Section exprD'_app.
    Variable ts : list Type.
    Variables tus tvs : tenv typ.

    Fixpoint apply' {T} (x : T) (ls : list {t : typ & T -> typD ts t}) t {struct ls} :
      typD ts (fold_right (@typ2 _ _ Fun _) t (map (@projT1 _ _) ls)) ->
      typD ts t :=
      match ls as ls
            return typD ts (fold_right (@typ2 _ _ Fun _) t (map (@projT1 _ _) ls)) ->
                   typD ts t
      with
        | nil => fun x => x
        | l :: ls => fun f =>
          apply' x ls _ (match typ2_cast ts (projT1 l) _ in _ = t return t with
                          | eq_refl => f
                        end (projT2 l x))
      end.

    Fixpoint apply_sem'
             (tf : typ) (e : OpenT ts tus tvs (typD ts tf))
             (ls : list (expr typ sym)) (t : typ)
             {struct ls}
    : option (OpenT ts tus tvs (typD ts t)) :=
      match ls with
        | nil =>
          match type_cast ts tf t with
            | None => None
            | Some cast => Some (Rcast (OpenT ts tus tvs) cast e)
          end
        | l :: ls =>
          typ2_match (F := Fun) (fun T => OpenT ts tus tvs T -> _) ts tf
                     (fun d r f =>
                        match exprD' ts tus tvs d l with
                          | None => None
                          | Some x =>
                            apply_sem' r (ap f x) ls t
                        end
                     )
                     (fun _ => None)
                     e
      end.

    Definition apps_sem'
               (e : expr typ sym) (l : list (expr typ sym)) (t : typ)
    : option (OpenT ts tus tvs (typD ts t)) :=
      match typeof_expr ts tus tvs e with
        | None => None
        | Some tf =>
          match exprD' ts tus tvs tf e with
            | Some f => apply_sem' _ f l t
            | None => None
          end
      end.

    Lemma apps_sem'_nil
    : forall e t,
        apps_sem' e nil t = exprD' ts tus tvs t e.
    Proof.
      intros. unfold apps_sem'.
      consider (typeof_expr ts tus tvs e); intros.
      { symmetry.
        rewrite ExprFacts.exprD'_type_cast; eauto.
        rewrite H. simpl.
        destruct (type_cast ts t0 t).
        { forward. destruct r. reflexivity. }
        { forward. } }
      { consider (exprD' ts tus tvs t e); auto; intros.
        exfalso.
        assert (exists v, exprD' ts tus tvs t e = Some v); eauto.
        eapply ExprFacts.exprD'_typeof_expr in H1. congruence. }
    Qed.

    Lemma exprD'_apps : forall es e t,
      exprD' ts tus tvs t (apps e es) = apps_sem' e es t.
    Proof.
      induction es; simpl; intros.
      { unfold apps_sem', apply_sem'.
        rewrite ExprFacts.exprD'_type_cast; eauto.
        forward.
        destruct (type_cast ts t0 t); destruct (exprD' ts tus tvs t0 e); auto.
        destruct r; reflexivity. }
      { rewrite IHes.
        unfold apps_sem'.
        simpl. forward. unfold type_of_apply.
        consider (typeof_expr ts tus tvs a); intros.
        { arrow_case ts t0; forward.
          { rewrite Relim_const in *.
            consider (exprD' ts tus tvs t0 e); intros.
            { Cases.rewrite_all_goal.
              consider (type_cast ts x t1); intros.
              { unfold Relim.
                repeat first [ rewrite eq_Const_eq | rewrite eq_Arr_eq ].
                autorewrite with exprD_rw; simpl; Cases.rewrite_all_goal.
                red in x1. subst.
                destruct r. Cases.rewrite_all_goal.
                forward. f_equal.
                unfold Open_App. simpl.
                repeat first [ rewrite eq_Const_eq | rewrite eq_Arr_eq ].
                reflexivity. }
              { repeat first [ rewrite eq_Const_eq | rewrite eq_Arr_eq ].
                rewrite ExprFacts.exprD'_type_cast; eauto.
                Cases.rewrite_all_goal.
                rewrite type_cast_sym_None; eauto.
                clear. destruct (typ2_cast ts x x0).
                destruct x1; reflexivity. } }
            { rewrite eq_Const_eq.
              consider (type_cast ts x t1); intros; auto.
              autorewrite with exprD_rw; simpl.
              Cases.rewrite_all_goal.
              forward. destruct r. clear - x1 H2 H4. destruct x1.
              congruence. } }
          { rewrite H1. auto. } }
        { arrow_case ts t0; forward.
          generalize (typ2_cast ts x x0); intros.
          rewrite ExprFacts.exprD'_type_cast; eauto.
          Cases.rewrite_all_goal.
          clear. destruct x1. destruct e0. reflexivity. } }
    Qed.

  End exprD'_app.

  (** TODO: Does this actually get used? *)
  Section exprD_app.
    Variables us vs : env nil.

    Fixpoint apply {T} (x : T) (ls : list {t : typ & T -> typD nil t}) t {struct ls} :
      typD nil (fold_right (@typ2 _ _ Fun _) t (map (@projT1 _ _) ls)) ->
      typD nil t :=
      match ls as ls
            return typD nil (fold_right (@typ2 _ _ Fun _) t (map (@projT1 _ _) ls)) ->
                   typD nil t
      with
        | nil => fun x => x
        | l :: ls => fun f =>
          apply x ls _ (match typ2_cast nil (projT1 l) _ in _ = t return t with
                          | eq_refl => f
                        end (projT2 l x))
      end.

    Definition apply_sem (tf : typ) (e : typD nil tf)
             (ls : list (expr typ sym)) (t : typ)
    : option (typD nil t) :=
      let (tus,us) := split_env us in
      let (tvs,vs) := split_env vs in
      match @apply_sem' nil tus tvs tf (fun _ _ => e) ls t with
        | None => None
        | Some f => Some (f us vs)
      end.

    Local Instance Expr_expr : Expr _ (expr typ sym) := Expr_expr.

    Definition apps_sem
               (e : expr typ sym) (l : list (expr typ sym)) (t : typ)
    : option (typD nil t) :=
      let (tus,us) := split_env us in
      let (tvs,vs) := split_env vs in
      match @apps_sem' nil tus tvs e l t with
        | None => None
        | Some f => Some (f us vs)
      end.

    Lemma apps_sem_nil : forall e t,
                           apps_sem e nil t = exprD us vs e t.
    Proof.
      intros. unfold apps_sem.
      unfold exprD.
      repeat match goal with
               | |- (let (_,_) := ?X in _) = (let (_,_) := ?Y in _) =>
                 change Y with X; destruct X
             end.
      rewrite apps_sem'_nil. simpl. reflexivity.
    Qed.

    Lemma exprD_apps : forall es e t,
      exprD us vs (apps e es) t = apps_sem e es t.
    Proof.
      unfold apps_sem, exprD.
      intros.
      repeat match goal with
               | |- (let (_,_) := ?X in _) = (let (_,_) := ?Y in _) =>
                 change Y with X; destruct X
             end.
      simpl. rewrite exprD'_apps. reflexivity.
    Qed.

  End exprD_app.
End app_full_proofs.
