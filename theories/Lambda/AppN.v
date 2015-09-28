Require Import ExtLib.Data.Pair.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Relations.TransitiveClosure.
Require Import ExtLib.Recur.Facts.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Util.Compat.
Require Import MirrorCore.Util.HListBuild.
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
  Variable Typ2_Fun : Typ2 _ RFun.
  Variable RSym_sym : RSym sym.

  Variable RTypeOk : RTypeOk.
  Variable Typ2Ok_Fun : Typ2Ok _.
  Variable RSymOk_sym : RSymOk _.

  Section apps_type.
    Variables tus tvs : tenv typ.

    Fixpoint type_of_applys (t : typ) (es : list (expr typ sym)) {struct es} : option typ :=
      match es with
        | nil => Some t
        | e :: es =>
          match typeof_expr tus tvs e with
            | Some t' =>
              typ2_match (fun _ => option _) t
                         (fun td tr =>
                            match type_cast t' td with
                              | Some _ => type_of_applys tr es
                              | _ => None
                            end)
                         None
            | _ => None
          end
      end.

    Definition typeof_apps (e : expr typ sym)
               (es : list (expr typ sym)) : option typ :=
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
        { arrow_case t.
          { rewrite Relim_const in *.
            consider (type_cast t0 x); intros.
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
            rewrite typ2_match_iota; eauto.
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
        typeof_expr tus tvs (apps e es) = typeof_apps e es.
    Proof.
      intros. unfold typeof_apps.
      consider (typeof_expr tus tvs e); intros.
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

  Lemma type_of_applys_circle_False_lem
  : forall tus tvs ls t t',
      type_of_applys tus tvs t ls = Some t' ->
      leftTrans (@tyAcc _ _) t t' ->
      False.
  Proof.
    induction ls; simpl in *; intros.
    { inv_all. subst.
      eapply (@irreflexivity _ _ (@wf_anti_sym _ _ (Relation.wf_leftTrans (@wf_tyAcc _ _ _)))) in H0.
      assumption. }
    { forward. arrow_case t.
      { rewrite Relim_const in *.
        rewrite eq_Const_eq in *. forward.
        clear H2. destruct r. symmetry in x1. destruct x1.
        eapply IHls in H3. auto.
        eapply LTStep. 2: eapply H0.
        eapply tyAcc_typ2R; eauto. }
      { congruence. } }
  Qed.

  Lemma type_of_applys_circle_False
  : forall tus tvs ls t t',
      type_of_applys tus tvs t ls = Some (typ2 t' t) -> False.
  Proof.
    intros. eapply type_of_applys_circle_False_lem.
    eassumption. constructor. eapply tyAcc_typ2R; eauto.
  Qed.

  Section exprD'_app.
    Variables tus tvs : tenv typ.

    Local Existing Instance Applicative_exprT.

    Fixpoint apply_sem'
             (tf : typ) (e : exprT tus tvs (typD tf))
             (ls : list (expr typ sym)) (t : typ)
             {struct ls}
    : option (exprT tus tvs (typD t)) :=
      match ls with
        | nil =>
          match type_cast tf t with
            | None => None
            | Some cast => Some (Rcast (exprT tus tvs) cast e)
          end
        | l :: ls =>
          typ2_match (F := RFun) (fun T => exprT tus tvs T -> _) tf
                     (fun d r f =>
                        match exprD' tus tvs d l with
                          | None => None
                          | Some x =>
                            apply_sem' r (Applicative.ap f x) ls t
                        end
                     )
                     (fun _ => None)
                     e
      end.

    Definition apps_sem'
               (e : expr typ sym) (l : list (expr typ sym)) (t : typ)
    : option (exprT tus tvs (typD t)) :=
      match typeof_expr tus tvs e with
        | None => None
        | Some tf =>
          match exprD' tus tvs tf e with
            | Some f => apply_sem' _ f l t
            | None => None
          end
      end.

    Lemma apps_sem'_nil
    : forall e t,
        apps_sem' e nil t = exprD' tus tvs t e.
    Proof.
      intros. unfold apps_sem'.
      consider (typeof_expr tus tvs e); intros.
      { symmetry.
        rewrite ExprFacts.exprD'_type_cast; eauto.
        rewrite H. simpl.
        destruct (type_cast t0 t).
        { forward. destruct r. reflexivity. }
        { forward. } }
      { consider (exprD' tus tvs t e); auto; intros.
        exfalso.
        assert (exists v, exprD' tus tvs t e = Some v); eauto.
        eapply ExprFacts.exprD'_typeof_expr in H1. congruence. }
    Qed.

    Lemma match_option_eta : forall T (a : option T),
        match a with
        | None => None
        | Some x => Some x
        end = a.
    Proof using.
      destruct a; reflexivity.
    Qed.

    Lemma exprD'_apps : forall es e t,
      exprD' tus tvs t (apps e es) = apps_sem' e es t.
    Proof.
      induction es; simpl; intros.
      { unfold apps_sem', apply_sem'.
        rewrite ExprFacts.exprD'_type_cast; eauto.
        forward.
        destruct (type_cast t0 t); destruct (exprD' tus tvs t0 e); auto.
        destruct r; reflexivity. }
      { rewrite IHes.
        unfold apps_sem'.
        simpl. forward. unfold type_of_apply.
        consider (typeof_expr tus tvs a); intros.
        { arrow_case t0; forward.
          { rewrite Relim_const in *.
            consider (exprD' tus tvs t0 e); intros.
            { Cases.rewrite_all_goal.
              consider (type_cast x t1); intros.
              { unfold Relim.
                autorewrite_with_eq_rw.
                autorewrite with exprD_rw; simpl; Cases.rewrite_all_goal.
                red in x1. subst.
                destruct r. Cases.rewrite_all_goal.
                forward. f_equal.
                unfold AbsAppI.exprT_App. simpl.
                autorewrite_with_eq_rw.
                repeat rewrite match_option_eta.
                match goal with
                | |- ?X = match ?X with _ => _ end =>
                  destruct X
                end; autorewrite with eq_rw; reflexivity. }
              { autorewrite_with_eq_rw.
                rewrite ExprFacts.exprD'_type_cast; eauto.
                Cases.rewrite_all_goal.
                rewrite type_cast_sym_None; eauto.
                clear. destruct (typ2_cast x x0).
                destruct x1; reflexivity. } }
            { rewrite eq_Const_eq.
              consider (type_cast x t1); intros; auto.
              autorewrite with exprD_rw; simpl.
              Cases.rewrite_all_goal.
              forward. destruct r. clear - x1 H2 H4. destruct x1.
              congruence. } }
          { rewrite H1. auto. } }
        { arrow_case t0; forward.
          generalize (typ2_cast x x0); intros.
          rewrite ExprFacts.exprD'_type_cast; eauto.
          Cases.rewrite_all_goal.
          clear. destruct x1. destruct e1. reflexivity. } }
    Qed.

    Fixpoint apply_fold t ts
             (es : HList.hlist (fun t => exprT tus tvs (typD t)) ts)
    :    exprT tus tvs (typD (fold_right (typ2 (F:=RFun)) t ts))
      -> exprT tus tvs (typD t) :=
      match es in HList.hlist _ ts
            return    exprT tus tvs (typD (fold_right (typ2 (F:=RFun)) t ts))
                   -> exprT tus tvs (typD t)
      with
      | HList.Hnil => fun f => f
      | HList.Hcons x xs => fun f =>
                              @apply_fold t _ xs (AbsAppI.exprT_App f x)
      end.

    Lemma apps_exprD'_fold_type
    : forall es e t eD,
        exprD' tus tvs t (apps e es) = Some eD ->
        exists ts fD esD,
          exprD' tus tvs (fold_right (typ2 (F:=RFun)) t ts) e = Some fD /\
          hlist_build_option
            (fun t => ExprI.exprT tus tvs (typD t))
            (fun t e => exprD' tus tvs t e) ts es = Some esD /\
          forall us vs,
            eD us vs = @apply_fold _ _ esD fD us vs.
    Proof using Typ2Ok_Fun RTypeOk RSymOk_sym.
      intros.
      rewrite exprD'_apps in H; eauto.
      unfold apps_sem' in H. forward. clear H.
      revert H0; revert H1; revert eD; revert t; revert e0; revert e.
      revert t0.
      induction es; simpl; intros.
      { exists nil. exists eD. exists HList.Hnil.
        simpl. split; eauto.
        forward. destruct r. inv_all; subst. assumption. }
      { arrow_case_any.
        { clear H.
          red in x1. subst.
          simpl in H1. autorewrite_with_eq_rw_in H1.
          forward; inv_all; subst.
          eapply IHes with (e := App e a) in H3; eauto.
          { forward_reason.
            assert (x0 = fold_right (typ2 (F:=RFun)) t x1).
            { autorewrite with exprD_rw in H2; simpl in H2.
              rewrite (exprD_typeof_Some _ _ _ _ _ H) in H2.
              rewrite H in H2.
              forward; inv_all; subst.
              eapply exprD_typeof_Some in H2; eauto.
              eapply exprD_typeof_Some in H0; eauto.
              rewrite H0 in H2.
              inv_all. assumption. }
            { subst.
              eexists (x :: x1). exists e0.
              eexists. split; eauto.
              split.
              { simpl.
                rewrite H3. rewrite H. reflexivity. }
              { simpl. intros.
                erewrite exprD'_App in H2; eauto.
                erewrite exprD_typeof_Some in H2 by eassumption.
                rewrite H0 in H2. rewrite H in H2.
                inv_all; subst. eauto. } } }
          { erewrite exprD'_App; eauto.
            erewrite exprD_typeof_Some by eassumption.
            rewrite H0; clear H0. rewrite H; clear H.
            unfold AbsAppI.exprT_App. autorewrite_with_eq_rw.
            reflexivity. } }
        { inversion H1. } }
    Qed.

  End exprD'_app.

(* DEAD CODE!
  (** TODO: Does this actually get used? *)
  Section exprD_app.
    Variables us vs : env.

    Fixpoint apply {T} (x : T) (ls : list {t : typ & T -> typD t}) t {struct ls} :
      typD (fold_right (@typ2 _ _ RFun _) t (map (@projT1 _ _) ls)) ->
      typD t :=
      match ls as ls
            return typD (fold_right (@typ2 _ _ RFun _) t (map (@projT1 _ _) ls)) ->
                   typD t
      with
        | nil => fun x => x
        | l :: ls => fun f =>
          apply x ls _ (match typ2_cast (projT1 l) _ in _ = t return t with
                          | eq_refl => f
                        end (projT2 l x))
      end.

    Definition apply_sem (tf : typ) (e : typD tf)
             (ls : list (expr typ sym)) (t : typ)
    : option (typD t) :=
      let (tus,us) := split_env us in
      let (tvs,vs) := split_env vs in
      match @apply_sem' tus tvs tf (fun _ _ => e) ls t with
        | None => None
        | Some f => Some (f us vs)
      end.

    Let Expr_expr : Expr _ (expr typ sym) := @Expr_expr _ _ _ _ _.
    Local Existing Instance Expr_expr.

    Definition apps_sem
               (e : expr typ sym) (l : list (expr typ sym)) (t : typ)
    : option (typD t) :=
      let (tus,us) := split_env us in
      let (tvs,vs) := split_env vs in
      match @apps_sem' tus tvs e l t with
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
*)
End app_full_proofs.
