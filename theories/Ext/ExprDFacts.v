Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.ExprCore.
Require Import MirrorCore.Ext.ExprT.
Require Import MirrorCore.Ext.ExprDI.

Set Implicit Arguments.
Set Strict Implicit.

(** This seems unavoidable if there are binders... **)
Require Import FunctionalExtensionality.

Module Build_ExprDenote (EDc : ExprDenote_core) <:
       ExprDenote with Definition exprD' := @EDc.exprD'.
  Require Import ExtLib.Data.ListNth.

  Include EDc.

  Section with_envs.
    Variable ts : types.
    Variable func : Type.
    Variable RSym_func : RSym (typD ts) func.

    Instance Expr_expr : @Expr typ (typD ts) (expr func) :=
      @Build_Expr _ (typD ts) (expr func)
                  exprD'
                  _
                  (@wf_expr_acc func).

    Theorem typeof_expr_exprD'_impl : forall tus tvs e t,
      typeof_expr tus tvs e = Some t ->
      exists val, exprD' tus tvs e t = Some val.
    Proof.
      Opaque lookup.
      intros tus tvs e; revert tvs.
      induction e; simpl; intros.
      { rewrite exprD'_Var.
        match goal with
          | |- context [ match ?X with _ => _ end ] =>
            consider X; intros
        end.
        { apply nth_error_get_hlist_nth_Some in H0.
          destruct H0. forward; subst; simpl in *.
          assert (t = x) by congruence; subst.
          rewrite typ_cast_typ_refl. eauto. }
        { apply nth_error_get_hlist_nth_None in H0. congruence. } }
      { rewrite exprD'_Sym.
        unfold symAs.
        generalize (symD f). rewrite H. intros.
        simpl.
        rewrite typ_cast_typ_refl. eauto. }
      { rewrite exprD'_App.
        specialize (IHe1 tvs). specialize (IHe2 tvs).
        repeat match goal with
                 | _ : match ?X with _ => _ end = _ |- _ =>
                   destruct X; try congruence
               end.
        specialize (IHe1 _ eq_refl). destruct IHe1.
        destruct t0; simpl in *; try congruence.
        change typ_eqb with (@rel_dec _ (@eq typ) _) in *.
        consider (t0_1 ?[ eq ] t1); intros; subst; try congruence.
        rewrite H0.
        destruct (IHe2 _ eq_refl). rewrite H.
        inv_all; subst. rewrite typ_cast_typ_refl.
        eauto. }
      { rewrite exprD'_Abs.
        specialize (IHe (t :: tvs)).
        destruct (typeof_expr tus (t :: tvs) e); try congruence.
        inv_all; subst.
        specialize (IHe _ eq_refl).
        destruct IHe.
        rewrite typ_cast_typ_refl. rewrite H. eauto. }
      { rewrite exprD'_UVar.
        match goal with
          | |- context [ match ?X with _ => _ end ] =>
            consider X; intros
        end.
        { apply nth_error_get_hlist_nth_Some in H0.
          destruct H0. forward; subst; simpl in *.
          assert (t = x) by congruence; subst.
          rewrite typ_cast_typ_refl. eauto. }
        { apply nth_error_get_hlist_nth_None in H0. congruence. } }
    Qed.

    Theorem exprD_Var : forall us ve u (t : typ),
      exprD us ve (Var u) t = lookupAs ve u t.
    Proof.
      unfold exprD; intros.
      consider (split_env ve); intros.
      destruct (split_env us).
      unfold lookupAs. simpl in *.
      rewrite exprD'_Var.
      match goal with
        | |- match match ?X with _ => _ end with _ => _ end = _ =>
          consider X; intros
      end.
      { forward; subst.
        apply nth_error_get_hlist_nth_Some in H1. simpl in *.
        destruct H1.
        consider (nth_error ve u); intros.
        { apply split_env_nth_error in H1.
          rewrite H in *. simpl in *.
          destruct s.
          specialize (H0 h).
          match goal with
            | H : _ = match _ with eq_refl => ?X end , H' : _ ?Y |- _ =>
              change Y with X in H'; generalize dependent X
          end.
          rewrite x2.
          intros; subst. inv_all; subst.
          destruct (typ_cast_typ ts nil x3 t); auto. }
        { exfalso. clear H0.
          apply split_env_nth_error_None in H1.
          rewrite H in *. simpl in *. congruence. } }
      { apply nth_error_get_hlist_nth_None in H0.
        consider (nth_error ve u); intros; auto.
        { destruct s. apply split_env_nth_error in H1.
          rewrite H in *. simpl in *.
          generalize dependent (hlist_nth h u).
          forward. } }
    Qed.

    Theorem exprD_UVar : forall us ve u t,
      exprD us ve (UVar u) t = lookupAs us u t.
    Proof.
      unfold exprD; intros.
      destruct (split_env ve).
      consider (split_env us); intros.
      unfold lookupAs. simpl in *.
      rewrite exprD'_UVar.
      match goal with
        | |- match match ?X with _ => _ end with _ => _ end = _ =>
          consider X; intros
      end.
      { forward; subst.
        apply nth_error_get_hlist_nth_Some in H1. simpl in *.
        destruct H1.
        consider (nth_error us u); intros.
        { apply split_env_nth_error in H1.
          rewrite H in *. simpl in *.
          destruct s.
          specialize (H0 h0).
          match goal with
            | H : _ = match _ with eq_refl => ?X end , H' : _ ?Y |- _ =>
              change Y with X in H'; generalize dependent X
          end.
          rewrite x2.
          intros; subst. inv_all; subst.
          destruct (typ_cast_typ ts nil x3 t); auto. }
        { exfalso. clear H0.
          apply split_env_nth_error_None in H1.
          rewrite H in *. simpl in *. congruence. } }
      { apply nth_error_get_hlist_nth_None in H0.
        consider (nth_error us u); intros; auto.
        { destruct s. apply split_env_nth_error in H1.
          rewrite H in *. simpl in *.
          generalize dependent (hlist_nth h0 u).
          forward. } }
    Qed.

    Theorem exprD_Sym : forall us ve f t,
      exprD us ve (Inj f) t = symAs f t.
    Proof.
      unfold exprD. intros.
      destruct (split_env ve).
      destruct (split_env us). simpl.
      rewrite exprD'_Sym.
      forward.
    Qed.

    Theorem exprD_App : forall us ve t e arg,
      exprD us ve (App e arg) t =
      match typeof_expr (typeof_env us) (typeof_env ve) e with
        | Some (tyArr l r) =>
          match exprD us ve e (tyArr l r)
              , exprD us ve arg l
              , typ_cast_typ _ _ r t
          with
            | Some f , Some x , Some cast =>
              Some (cast (fun x => x) (f x))
            | _ , _ , _ => None
          end
        | _ => None
      end.
    Proof.
      unfold exprD; intros.
      unfold typeof_env.
      rewrite <- (split_env_projT1 ve).
      rewrite <- (split_env_projT1 us).
      destruct (split_env ve). destruct (split_env us). simpl; intros.
      rewrite exprD'_App.
      simpl in *.
      forward.
      repeat match goal with
               | |- match match ?X with _ => _ end with _ => _ end =
                    match ?Y with _ => _ end =>
                 change X with Y; destruct Y; auto
             end.
    Qed.

    Theorem exprD_Abs_is_arr : forall us vs e t t',
      exprD us vs (Abs t' e) t =
      match t as t return option (typD ts nil t) with
        | tyArr l r =>
          if t' ?[ eq ] l then
            exprD us vs (Abs l e) (tyArr l r)
          else None
        | _ => None
      end.
    Proof.
      unfold exprD.
      intros; destruct (split_env vs); destruct (split_env us).
      simpl.
      rewrite exprD'_Abs.
      destruct t; auto.
      rewrite exprD'_Abs.
      consider (t' ?[ eq ] t1); intros; subst; try reflexivity.
      match goal with
        | |- match match ?x with _ => _ end with _ => _ end = _ =>
          consider x; intros; auto
      end.
      generalize (@typ_cast_typ_eq _ _ _ _ _ H0).
      congruence.
    Qed.

    Theorem exprD_Abs : forall us vs e t t' v,
      exprD us vs (Abs t' e) t = Some v ->
      exists tr (pf : t = tyArr t' tr)
             (pf' : forall a : typD ts nil t',
                      exprD us (existT (typD ts nil) _ a :: vs) e tr = None ->
                      False),
        match pf in _ = t return typD ts nil t with
          | eq_refl => v
        end = fun x => match exprD us (existT _ t' x :: vs) e tr as z
                             return (z = None -> False) -> typD ts nil tr
                       with
                         | Some x => fun _ => x
                         | None => fun pf => match pf eq_refl with end
                       end (pf' x).
    Proof.
      unfold exprD. simpl; intros.
      destruct (split_env us).
      consider (split_env vs); intros.
      forward. inv_all. subst. simpl.
      rewrite exprD'_Abs in H0.
      forward. inv_all; subst.
      exists t1.
      pose proof (typ_cast_typ_eq _ _ _ _ H1); subst.
      rewrite typ_cast_typ_refl in H1. inv_all; subst.
      exists eq_refl. simpl.
      rewrite H2.
      assert (forall a : typD ts nil t', Some (t3 h (Hcons a h0)) = None -> False).
      congruence.
      exists H0. reflexivity.
    Qed.

    Theorem typeof_expr_eq_exprD_False : forall us ve l e t,
      WellTyped_expr (typeof_env us) (l :: typeof_env ve) e t ->
      forall x, exprD us (existT _ l x :: ve) e t = None ->
                False.
    Proof.
      intros. unfold exprD in *. simpl in *.
      consider (split_env us).
      unfold WellTyped_expr in *.
      eapply typeof_expr_exprD'_impl in H. destruct H.
      generalize (projT2 (split_env ve)).
      rewrite split_env_projT1.
      intros.
      forward.
      cut (typeof_env us = x1).
      { intros; subst.
        unfold typeof_env in *. congruence. }
      { clear - H0.
        unfold typeof_env.
        eapply map_projT1_split_env. eassumption. }
    Qed.

    Lemma lem_typeof_expr_exprD' : forall tus vs e t,
      WellTyped_expr tus vs e t <->
      exprD' tus vs e t <> None.
    Proof.
      intros tus vs e. revert vs. induction e; simpl; intros.
      { rewrite WellTyped_expr_Var.
        rewrite exprD'_Var.
        match goal with
          | |- _ <-> match ?X with _ => _ end <> _ =>
            consider X; intros
        end.
        { apply nth_error_get_hlist_nth_Some in H.
          destruct H. forward. subst. simpl in *.
          rewrite x0. split; intros.
          { inv_all; subst. rewrite typ_cast_typ_refl. congruence. }
          { match type of H with
              | context [ match ?X with _ => _ end ] =>
                consider X; intros
            end.
            { apply typ_cast_typ_eq in H. f_equal; auto. }
            { congruence. } } }
        { apply nth_error_get_hlist_nth_None in H. rewrite H.
          intuition congruence. } }
      { rewrite WellTyped_expr_Sym.
        rewrite exprD'_Sym.
        unfold symAs.
        generalize (symD f).
        destruct (typeof_sym f); intuition; try congruence.
        { inv_all; subst. simpl in *.
          rewrite typ_cast_typ_refl in *. congruence. }
        { simpl in *. forward.
          inv_all; subst.
          generalize (typ_cast_typ_eq _ _ _ _ H); intros.
          f_equal; auto. } }
      { rewrite WellTyped_expr_App.
        rewrite exprD'_App.
        split; intros.
        { destruct H. destruct H.
          rewrite IHe1 in *. rewrite IHe2 in *.
          destruct H. destruct H0.
          consider (typeof_expr tus vs e1); intros.
          { generalize H. generalize H0.
            eapply IHe1 in H. eapply IHe2 in H0.
            red in H; red in H0. rewrite H in H2. inv_all; subst.
            destruct t0; simpl in *; try congruence.
            change typ_eqb with (@rel_dec _ (@eq typ) _) in *.
            consider (t0_1 ?[ eq ] x0); try congruence; intros; inv_all; subst.
            destruct (exprD' tus vs e1 (tyArr x0 t)); intuition.
            destruct (exprD' tus vs e2 x0); intuition.
            rewrite typ_cast_typ_refl in H1; congruence. }
          { exfalso.
            eapply IHe1 in H. red in H. congruence. } }
        { consider (typeof_expr tus vs e1);
          try congruence; intros.
          destruct t0; try congruence.
          repeat match goal with
                   | _ : not (match ?X with _ => _ end = _) |- _ =>
                     consider X; intros
                 end; try congruence.
          generalize (typ_cast_typ_eq _ _ _ _ H2); intros.
          consider (exprD' tus vs e1 (tyArr t0_1 t0_2)); intros; try congruence.
          inv_all. rewrite H5 in *.
          exists (tyArr t0_1 t0_2). exists t0_1.
          simpl.
          change typ_eqb with (@rel_dec _ (@eq typ) _) in *.
          consider (t0_1 ?[ eq ] t0_1); try congruence; intros.
          rewrite IHe1. rewrite IHe2.
          rewrite H4 in *. eapply typeof_expr_exprD'_impl in H.
          destruct H. rewrite H. rewrite H1. intuition congruence. } }
      { rewrite WellTyped_expr_Abs.
        rewrite exprD'_Abs.
        { split; intros.
          { destruct H. destruct H; subst.
            rewrite typ_cast_typ_refl.
            consider (exprD'  tus (t :: vs) e x); try congruence.
            intros. intro. eapply IHe; eauto. }
          { destruct t0; intuition try congruence.
            repeat match goal with
                     | _ : match ?x with _ => _ end = _ -> False |- _ =>
                       consider x; intuition
                   end.
            generalize (typ_cast_typ_eq _ _ _ _ H); intro; subst.
            exists t0_2. intuition.
            eapply IHe. rewrite H0. congruence. } } }
      { rewrite WellTyped_expr_UVar.
        rewrite exprD'_UVar.
        match goal with
          | |- _ <-> match ?X with _ => _ end <> _ =>
            consider X; intros
        end.
        { apply nth_error_get_hlist_nth_Some in H.
          destruct H. forward. subst. simpl in *.
          rewrite x0. split; intros.
          { inv_all; subst. rewrite typ_cast_typ_refl. congruence. }
          { match type of H with
              | context [ match ?X with _ => _ end ] =>
                consider X; intros
            end.
            { apply typ_cast_typ_eq in H. f_equal; auto. }
            { congruence. } } }
        { apply nth_error_get_hlist_nth_None in H. rewrite H.
          intuition congruence. } }
    Qed.

    Theorem typeof_expr_exprD' : forall tus vs e t,
      WellTyped_expr tus vs e t <->
      exists v, exprD' tus vs e t = Some v.
    Proof.
      intros.
      rewrite lem_typeof_expr_exprD'.
      intuition.
      destruct (exprD' tus vs e t); intuition. eauto.
      destruct H. congruence.
    Qed.

    Theorem typeof_expr_exprD : forall us vs e t,
      WellTyped_expr (typeof_env us) (typeof_env vs) e t <->
      exists v, exprD us vs e t = Some v.
    Proof.
      intros. rewrite typeof_expr_exprD'.
      unfold exprD.
      consider (split_env us); intros.
      consider (split_env vs); intros.
      assert (x0 = typeof_env vs).
      { clear - H0. unfold typeof_env.
        rewrite <- split_env_projT1. rewrite H0. reflexivity. }
      assert (x = typeof_env us).
      { clear - H. unfold typeof_env.
        rewrite <- split_env_projT1. rewrite H. reflexivity. }
      subst. intuition.
      { destruct H1. simpl.
        eexists. simpl.
        match goal with
          | H : ?X = _ |- match ?Y with _ => _ end = _ =>
            change Y with X ; rewrite H; auto
        end. }
      { destruct H1.
        match goal with
          | H : match ?X with _ => _ end = _ |- exists v, ?Y = _ =>
            change Y with X ; destruct X ; try congruence
        end. eauto. }
    Qed.

    Lemma typeof_expr_exprD_same_type : forall us vs e t t' v,
      exprD us vs e t = Some v ->
      typeof_expr (typeof_env us) (typeof_env vs) e = Some t' ->
      t = t'.
    Proof.
      intros.
      assert (exists v, exprD us vs e t = Some v); eauto.
      eapply typeof_expr_exprD in H1.
      red in H1. rewrite H1 in *. inv_all; subst. reflexivity.
    Qed.

    Theorem exprD'_type_cast
    : forall tus tvs e t,
        exprD' tus tvs e t =
        match typeof_expr tus tvs e with
          | None => None
          | Some t' =>
            match typ_cast_typ ts nil t' t with
              | None => None
              | Some cast =>
                match exprD' tus tvs e t' with
                  | None => None
                  | Some x =>
                    Some (fun us gs => cast (fun x => x) (x us gs))
                end
            end
        end.
    Proof.
      intros tus tvs e; revert tvs.
      induction e; simpl; intros.
      { repeat match goal with
                 | |- context [ match ?X with _ => _ end ] =>
                   consider X; intros
               end.
        { rewrite exprD'_Var in *.
          generalize (typ_cast_typ_eq _ _ _ _ H0); intros; subst.
          rewrite H1.
          rewrite typ_cast_typ_refl in H0.
          inv_all; subst. reflexivity. }
        { generalize (typ_cast_typ_eq _ _ _ _ H0); intros; subst; congruence. }
        { rewrite exprD'_Var.
          forward.
          exfalso. subst. apply nth_error_get_hlist_nth_Some in H2.
          simpl in *. forward_reason.
          clear H1. rewrite H in *. inv_all; subst.
          match goal with
            | H : ?X = None , H' : ?Y = Some _ |- _ =>
              change X with Y in H ; congruence
          end. }
        { rewrite exprD'_Var.
          eapply nth_error_get_hlist_nth_None in H.
          rewrite H. reflexivity. } }
      { repeat match goal with
                 | |- context [ match ?X with _ => _ end ] =>
                   consider X; intros
               end.
        { rewrite exprD'_Sym in *.
          unfold symAs in *.
          generalize dependent (symD f).
          rewrite H. simpl; intros.
          rewrite typ_cast_typ_refl in *. inv_all; subst.
          generalize (typ_cast_typ_eq _ _ _ _ H0); intros; subst.
          rewrite typ_cast_typ_refl in *. inv_all; subst.
          reflexivity. }
        { generalize (typ_cast_typ_eq _ _ _ _ H0); intros; subst.
          auto. }
        { rewrite exprD'_Sym. unfold symAs.
          generalize (symD f). rewrite H.
          simpl. intros.
          match goal with
            | H : ?X = _ |- match match ?Y with _ => _ end with _ => _ end = _ =>
              change Y with X ; rewrite H
          end. auto. }
        { rewrite exprD'_Sym. unfold symAs.
          generalize (symD f).
          rewrite H. auto. } }
      { rewrite exprD'_App.
        specialize (IHe1 tvs); specialize (IHe2 tvs).
        consider (typeof_expr tus tvs e1); intros; auto.
        consider (typeof_expr tus tvs e2); intros.
        { destruct t0; simpl in *; auto.
          consider (typ_eqb t0_1 t1).
          { intros; subst.
            rewrite IHe1; clear IHe1.
            rewrite IHe2; clear IHe2.
            repeat rewrite typ_cast_typ_refl.
            rewrite exprD'_App. Cases.rewrite_all_goal.
            match goal with
              | |- _ = match ?X with _ => _ end =>
                consider X; intros
            end; intros.
            { generalize (typ_cast_typ_eq _ _ _ _ H1); intros; subst.
              forward.
              rewrite typ_cast_typ_refl in H1.
              rewrite typ_cast_typ_refl in H4.
              inv_all; subst. auto. }
            { match goal with
                | H : ?X = _ |- context [ ?Y ] =>
                  change Y with X ; rewrite H
              end.
              forward. } }
          { intros.
            rewrite IHe1.
            rewrite typ_cast_typ_refl.
            rewrite IHe2.
            rewrite typ_cast_typ_neq by auto.
            forward. } }
        { destruct t0; auto.
          rewrite IHe1.
          rewrite typ_cast_typ_refl.
          rewrite H1. forward. } }
      { specialize (IHe (t :: tvs)).
        rewrite exprD'_Abs.
        consider (typeof_expr tus (t :: tvs) e); intros.
        { destruct t0; try rewrite typ_cast_typ_neq by congruence; auto.
          rewrite exprD'_Abs.
          rewrite typ_cast_typ_refl.
          rewrite IHe; clear IHe.
          match goal with
            | |- _ = match ?X with _ => _ end =>
              consider X; intros
          end.
          { generalize (typ_cast_typ_eq  _ _ _ _ H0).
            intros. inversion H1; clear H1; subst.
            repeat rewrite typ_cast_typ_refl in *.
            inv_all; subst.
            forward. }
          { eapply typ_cast_typ_neq' in H0.
            forward. exfalso.
            apply H0. f_equal.
            generalize (typ_cast_typ_eq _ _ _ _ H1); intros; auto.
            generalize (typ_cast_typ_eq _ _ _ _ H2); intros; auto. } }
        { destruct t0; auto.
          rewrite H0. forward. } }
      { rewrite exprD'_UVar. unfold lookupAs.
        match goal with
          | |- match ?X with _ => _ end = _ =>
            consider X; intros
        end.
        { generalize H.
          apply nth_error_get_hlist_nth_Some in H.
          forward. subst; simpl in *.
          destruct H0. rewrite x0.
          match goal with
            | |- match ?X with _ => _ end =
                 match ?Y with _ => _ end =>
              change Y with X; forward
          end.
          rewrite exprD'_UVar.
          rewrite H1.
          rewrite typ_cast_typ_refl. reflexivity. }
        { apply nth_error_get_hlist_nth_None in H. rewrite H.
          reflexivity. } }
    Qed.

    Theorem exprD_type_cast
    : forall us vs e t,
        exprD us vs e t =
        match typeof_expr (typeof_env us) (typeof_env vs) e with
          | None => None
          | Some t' =>
            match typ_cast_typ ts nil t' t with
              | None => None
              | Some cast =>
                match exprD us vs e t' with
                  | None => None
                  | Some x =>
                    Some (cast (fun x => x) x)
                end
            end
        end.
    Proof.
      intros. unfold exprD.
      consider (split_env vs); intros.
      consider (split_env us); intros.
      simpl.
      rewrite exprD'_type_cast.
      assert (x = typeof_env vs).
      { unfold typeof_env.
        rewrite <- split_env_projT1. rewrite H. reflexivity. }
      assert (x0 = typeof_env us).
      { unfold typeof_env.
        rewrite <- split_env_projT1. rewrite H0. reflexivity. }
      subst.
      forward.
      match goal with
        | |- match match ?X with _ => _ end with _ => _ end =
             match ?Y with _ => _ end =>
          change Y with X
      end.
      forward.
    Qed.

    Theorem typeof_expr_weaken
    : forall (e : expr func) uenv venv t,
        typeof_expr uenv venv e = Some t ->
        forall ue ve,
          typeof_expr (uenv ++ ue) (venv ++ ve) e = Some t.
    Proof.
      induction e; simpl; intros; forward; inv_all; subst; Cases.rewrite_all_goal ;
      eauto using nth_error_weaken.
      { specialize (IHe uenv (t :: venv) t1).
        simpl in *.
        Cases.rewrite_all_goal. auto. }
    Qed.

    Theorem exprD'_weaken
    : forall (tus : tenv typ) (tvs : tenv typ)
             (e : expr func) (t : typ)
             (val : hlist (typD ts nil) tus ->
                    hlist (typD ts nil) tvs -> typD ts nil t),
        @exprD' _ func RSym_func tus tvs e t = Some val ->
        forall tus' tvs',
        exists val',
          @exprD' ts func RSym_func (tus ++ tus') (tvs ++ tvs') e t = Some val' /\
          (forall (us : hlist (typD ts nil) tus) (vs : hlist (typD ts nil) tvs)
                  (us' : hlist (typD ts nil) tus') vs',
             val us vs = val' (hlist_app us us') (hlist_app vs vs')).
    Proof.
      intros tus tvs e. revert tvs.
      induction e; simpl; intros.
      { rewrite exprD'_Var in *.
        forward; subst; inv_all; subst.
        eapply nth_error_get_hlist_nth_weaken with (ls' := tvs') in H0.
        forward_reason. simpl in *.
        rewrite H. rewrite H1. eexists; split; eauto.
        simpl; intros. rewrite <- H0. reflexivity. }
      { rewrite exprD'_Sym in *.
        forward. inv_all; subst.
        eexists; split; eauto. }
      { rewrite exprD'_App in *.
        forward; inv_all; subst.
        eapply typeof_expr_weaken with (ue := tus') (ve := tvs') in H0.
        eapply IHe1 in H1.
        eapply IHe2 in H2. forward_reason.
        Cases.rewrite_all_goal.
        eexists; split; eauto.
        simpl. intros.
        f_equal. rewrite <- H4. rewrite <- H2. reflexivity. }
      { rewrite exprD'_Abs in *.
        forward; inv_all; subst.
        eapply IHe in H1.
        forward_reason. simpl in *.
        rewrite H.
        eexists; split; eauto.
        simpl; intros.
        apply functional_extensionality.
        intro.
        apply (H1 us (@Hcons _ (typD ts nil) _ _ (p (fun x => x) x0) vs)). }
      { rewrite exprD'_UVar in *.
        forward; subst; inv_all; subst.
        eapply nth_error_get_hlist_nth_weaken with (ls' := tus') in H0.
        forward_reason. simpl in *.
        rewrite H. rewrite H1. eexists; split; eauto.
        simpl; intros. rewrite <- H0. reflexivity. }
    Qed.

    Lemma nth_error_get_hlist_nth_appL
    : forall t (F : t -> Type) tvs' tvs n,
        n < length tvs ->
        exists x,
          nth_error_get_hlist_nth F (tvs ++ tvs') n = Some x /\
          exists y,
            nth_error_get_hlist_nth F tvs n = Some (@existT _ _ (projT1 x) y) /\
            forall vs vs',
              (projT2 x) (hlist_app vs vs') = y vs.
    Proof.
      clear. induction tvs; simpl; intros.
      { exfalso; inversion H. }
      { destruct n.
        { clear H IHtvs.
          eexists; split; eauto. eexists; split; eauto.
          simpl. intros. rewrite (hlist_eta vs). reflexivity. }
        { apply Lt.lt_S_n in H.
          { specialize (IHtvs _ H).
            forward_reason.
            rewrite H0. rewrite H1.
            forward. subst. simpl in *.
            eexists; split; eauto.
            eexists; split; eauto. simpl.
            intros. rewrite (hlist_eta vs). simpl. auto. } } }
    Qed.

    Lemma nth_error_get_hlist_nth_appR
    : forall t (F : t -> Type) tvs' tvs n x,
        n >= length tvs ->
        nth_error_get_hlist_nth F (tvs ++ tvs') n = Some x ->
        exists y,
          nth_error_get_hlist_nth F tvs' (n - length tvs) = Some (@existT _ _ (projT1 x) y) /\
          forall vs vs',
            (projT2 x) (hlist_app vs vs') = y vs'.
    Proof.
      clear. induction tvs; simpl; intros.
      { cutrewrite (n - 0 = n); [ | omega ].
        rewrite H0. destruct x. simpl.
        eexists; split; eauto. intros.
        rewrite (hlist_eta vs). reflexivity. }
      { destruct n.
        { inversion H. }
        { assert (n >= length tvs) by omega. clear H.
          { forward. inv_all; subst. simpl in *.
            specialize (IHtvs _ _ H1 H0).
            simpl in *.
            forward_reason.
            rewrite H.
            eexists; split; eauto.
            intros. rewrite (hlist_eta vs). simpl. auto. } } }
    Qed.

    Theorem exprD'_Var_App_L : forall tus tvs' t tvs v,
      v < length tvs ->
      match exprD' tus (tvs ++ tvs') (Var v) t , exprD' tus tvs (Var v) t with
        | None , None => True
        | Some val , Some val' =>
          forall us vs vs',
            val us (hlist_app vs vs') = val' us vs
        | _ , _ => False
      end.
    Proof.
      intros. repeat rewrite exprD'_Var.
      eapply nth_error_get_hlist_nth_appL with (tvs := tvs) (tvs' := tvs') (F := typD ts nil) in H; eauto with typeclass_instances.
      forward_reason.
      repeat match goal with
               | H : ?X = _ |- context [ ?Y ] =>
                 change Y with X; rewrite H
             end.
      destruct x; simpl in *. forward.
      rewrite H1. auto.
    Qed.

    Theorem exprD'_Var_App_R : forall tus tvs' t tvs v,
      v >= length tvs ->
      match exprD' tus (tvs ++ tvs') (Var v) t
          , exprD' tus tvs' (Var (v - length tvs)) t with
        | None , None => True
        | Some val , Some val' =>
          forall us vs vs',
            val us (hlist_app vs vs') = val' us vs'
        | _ , _ => False
      end.
    Proof.
      intros. repeat rewrite exprD'_Var.
      match goal with
        | |- match match ?X with _ => _ end with _ => _ end =>
          consider X
      end; intros.
      { forward. subst.
        eapply nth_error_get_hlist_nth_appR in H1; eauto with typeclass_instances.
        simpl in *. forward_reason.
        rewrite H0.
        forward. f_equal. apply H1. }
      { forward.
        rewrite nth_error_get_hlist_nth_None in H0.
        rewrite nth_error_app_R in H0; auto.
        rewrite <- nth_error_get_hlist_nth_None with (F := typD ts nil) in H0.
        clear - H0 H2.
        match goal with
          | H : ?X = _ , H' : ?Y = _ |- _ =>
            change Y with X in H' ; rewrite H in H'
        end. congruence. }
    Qed.

    Theorem exprD_Var_App_L : forall us vs' t vs v,
      v < length vs ->
      exprD us (vs ++ vs') (Var v) t = exprD us vs (Var v) t.
    Proof.
      intros.
      generalize (@exprD'_Var_App_L (typeof_env us) (typeof_env vs') t (typeof_env vs) v).
      rewrite typeof_env_length.
      intro X; specialize (X H).
      unfold exprD.
      rewrite split_env_app.
      consider (split_env vs); consider (split_env vs'); intros.
      assert (x0 = typeof_env vs).
      { unfold typeof_env. rewrite <- split_env_projT1. rewrite H1. reflexivity. }
      assert (x = typeof_env vs').
      { unfold typeof_env. rewrite <- split_env_projT1. rewrite H0. reflexivity. }
      subst.
      consider (split_env us). intros. simpl.
      assert (x = typeof_env us).
      { unfold typeof_env. rewrite <- split_env_projT1. rewrite H2. reflexivity. }
      subst.
      destruct (exprD' (typeof_env us) (typeof_env vs ++ typeof_env vs') (Var v) t);
        destruct (exprD' (typeof_env us) (typeof_env vs) (Var v) t); intuition.
      { rewrite X. auto. }
    Qed.

    Theorem exprD_Var_App_R : forall us vs' t vs v,
      v >= length vs ->
      exprD us (vs ++ vs') (Var v) t = exprD us vs' (Var (v - length vs)) t.
    Proof.
      intros.
      generalize (@exprD'_Var_App_R (typeof_env us) (typeof_env vs') t (typeof_env vs) v).
      rewrite typeof_env_length.
      intro X; specialize (X H).
      unfold exprD.
      rewrite split_env_app.
      consider (split_env vs); consider (split_env vs'); consider (split_env us); intros.
      assert (x1 = typeof_env vs).
      { unfold typeof_env. rewrite <- split_env_projT1. rewrite H2. reflexivity. }
      assert (x0 = typeof_env vs').
      { unfold typeof_env. rewrite <- split_env_projT1. rewrite H1. reflexivity. }
      assert (x = typeof_env us).
      { unfold typeof_env. rewrite <- split_env_projT1. rewrite H0. reflexivity. }
      subst.
      simpl.
      repeat match goal with
               | H : match ?X with _ => _ end |- context [ ?Y ] =>
                 change Y with X; consider X; intros
             end; intuition.
      { rewrite X. auto. }
    Qed.

    Theorem exprD'_UVar_App_L : forall tus tus' t tvs v,
      v < length tus ->
      match exprD' (tus ++ tus') tvs (UVar v) t , exprD' tus tvs (UVar v) t with
        | None , None => True
        | Some val , Some val' =>
          forall us us' vs,
            val (hlist_app us us') vs = val' us vs
        | _ , _ => False
      end.
    Proof.
      intros. repeat rewrite exprD'_UVar.
      eapply nth_error_get_hlist_nth_appL with (tvs := tus) (tvs' := tus') (F := typD ts nil) in H; eauto with typeclass_instances.
      forward_reason.
      repeat match goal with
               | H : ?X = _ |- context [ ?Y ] =>
                 change Y with X; rewrite H
             end.
      destruct x; simpl in *. forward.
      rewrite H1. auto.
    Qed.

    Theorem exprD'_UVar_App_R : forall tus tus' t tvs v,
      v >= length tus ->
      match exprD' (tus ++ tus') tvs (UVar v) t
          , exprD' tus' tvs (UVar (v - length tus)) t with
        | None , None => True
        | Some val , Some val' =>
          forall us us' vs,
            val (hlist_app us us') vs = val' us' vs
        | _ , _ => False
      end.
    Proof.
      intros. repeat rewrite exprD'_UVar.
      match goal with
        | |- match match ?X with _ => _ end with _ => _ end =>
          consider X
      end; intros.
      { forward. subst.
        eapply nth_error_get_hlist_nth_appR in H1; eauto with typeclass_instances.
        simpl in *. forward_reason.
        rewrite H0.
        forward. f_equal. apply H1. }
      { forward.
        rewrite nth_error_get_hlist_nth_None in H0.
        rewrite nth_error_app_R in H0; auto.
        rewrite <- nth_error_get_hlist_nth_None with (F := typD ts nil) in H0.
        clear - H0 H2.
        match goal with
          | H : ?X = _ , H' : ?Y = _ |- _ =>
            change Y with X in H' ; rewrite H in H'
        end. congruence. }
    Qed.

    Theorem exprD_UVar_App_L : forall us us' vs t v,
      v < length us ->
      exprD (us ++ us') vs (UVar v) t = exprD us vs (UVar v) t.
    Proof.
      intros.
      generalize (@exprD'_UVar_App_L (typeof_env us) (typeof_env us') t (typeof_env vs) v).
      rewrite typeof_env_length.
      intro X; specialize (X H).
      unfold exprD.
      rewrite split_env_app.
      consider (split_env us); consider (split_env us'); intros.
      assert (x = typeof_env us').
      { unfold typeof_env. rewrite <- split_env_projT1. rewrite H0. reflexivity. }
      assert (x0 = typeof_env us).
      { unfold typeof_env. rewrite <- split_env_projT1. rewrite H1. reflexivity. }
      subst.
      consider (split_env vs). intros. simpl.
      assert (x = typeof_env vs).
      { unfold typeof_env. rewrite <- split_env_projT1. rewrite H2. reflexivity. }
      subst.
      destruct (exprD' (typeof_env us ++ typeof_env us') (typeof_env vs) (UVar v) t);
        destruct (exprD' (typeof_env us) (typeof_env vs) (UVar v) t); intuition.
      { rewrite X. auto. }
    Qed.

    Theorem exprD_UVar_App_R : forall us us' vs t v,
      v >= length us ->
      exprD (us ++ us') vs (UVar v) t = exprD us' vs (UVar (v - length us)) t.
    Proof.
      intros.
      generalize (@exprD'_UVar_App_R (typeof_env us) (typeof_env us') t (typeof_env vs) v).
      rewrite typeof_env_length.
      intro X; specialize (X H).
      unfold exprD.
      rewrite split_env_app.
      consider (split_env vs); consider (split_env us'); consider (split_env us); intros.
      assert (x1 = typeof_env vs).
      { unfold typeof_env. rewrite <- split_env_projT1. rewrite H2. reflexivity. }
      assert (x0 = typeof_env us').
      { unfold typeof_env. rewrite <- split_env_projT1. rewrite H1. reflexivity. }
      assert (x = typeof_env us).
      { unfold typeof_env. rewrite <- split_env_projT1. rewrite H0. reflexivity. }
      subst.
      simpl.
      repeat match goal with
               | H : match ?X with _ => _ end |- context [ ?Y ] =>
                 change Y with X; consider X; intros
             end; intuition.
      { rewrite X. auto. }
    Qed.

    Theorem exprD'_var_env
    : forall us vs vs' e t (H : vs' = vs),
        exprD' us vs e t =
        match H in _ = vs
              return option (_ -> hlist (typD ts nil) vs -> typD ts nil t)
        with
          | eq_refl => exprD' us vs' e t
        end.
    Proof.
      intros. uip_all. reflexivity.
    Qed.

    Theorem exprD'_uvar_env
    : forall us us' vs e t (H : us' = us),
        exprD' us vs e t =
        match H in _ = us
              return option (hlist (typD ts nil) us -> _ -> typD ts nil t)
        with
          | eq_refl => exprD' us' vs e t
        end.
    Proof.
      intros. uip_all. reflexivity.
    Qed.

  End with_envs.

End Build_ExprDenote.
