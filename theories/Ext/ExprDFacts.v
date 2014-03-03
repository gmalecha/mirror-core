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
                  (@WellTyped_expr ts func _)
                  _
                  (@wf_expr_acc func).


(*
    Theorem exprD'_var_env
    : forall vs vs' e t (H : vs' = vs),
        exprD' e t us vs = match H in _ = vs
                                 return option (hlist (typD ts nil) vs -> typD ts nil t)
                           with
                             | eq_refl => exprD' us vs' e t
                           end.
    Proof.
      intros. uip_all. reflexivity.
    Qed.
*)

    Theorem typeof_expr_exprD'_impl : forall tus tvs e t,
      typeof_expr tus tvs e = Some t ->
      exists val, exprD' tus tvs e t = Some val.
    Proof.
      Opaque lookup.
      intros tus tvs e; revert tvs.
      induction e; simpl; intros.
      { rewrite exprD'_Var.
        match goal with
          | |- context [ @eq_refl ?A ?B ] =>
            generalize (@eq_refl A B)
        end.
        revert H.
        generalize (nth_error tvs v) at 1 2 4.
        intros. subst.
        rewrite typ_cast_typ_refl. eauto. }
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
          | |- context [ @eq_refl ?A ?B ] =>
            generalize (@eq_refl A B)
        end.
        revert H.
        generalize (nth_error tus u) at 1 2 4.
        intros. subst.
        rewrite typ_cast_typ_refl. eauto. }
    Qed.

    Theorem exprD_Var : forall us ve u (t : typ),
      exprD us ve (Var u) t = lookupAs ve u t.
    Proof.
      unfold exprD; intros.
      consider (split_env ve); intros.
      destruct (split_env us).
      unfold lookupAs.
      consider (nth_error ve u); intros.
      { eapply split_env_nth_error in H0. simpl.
        rewrite exprD'_Var.
        rewrite H in *. simpl in *.
        destruct s.
        match goal with
          | |- context [ @eq_refl ?X ?Y ] =>
            generalize (@eq_refl X Y)
        end.
        revert H0.
(*
        change (
            let zzz e := hlist_nth e u in
            match
              nth_error x u as t1
              return
              (match t1 with
                 | Some v => typD ts nil v
                 | None => unit
               end -> Prop)
            with
              | Some v =>
                fun res : typD ts nil v =>
                  existT (typD ts nil) x0 t0 = existT (typD ts nil) v res
              | None => fun _ : unit => False
            end (zzz h) ->
            forall e : nth_error x u = nth_error x u,
              match
                match
                  nth_error x u as z
                  return
                  (z = nth_error x u ->
                   option (hlist (typD ts nil) x -> typD ts nil t))
                with
                  | Some z =>
                    fun pf : Some z = nth_error x u =>
                      match typ_cast_typ ts nil z t with
                        | Some cast =>
                          Some
                            (fun e0 : hlist (typD ts nil) x =>
                               match
                                 pf in (_ = t'')
                                 return
                                 (match t'' with
                                    | Some t1 => typD ts nil t1
                                    | None => unit
                                  end -> typD ts nil t)
                               with
                                 | eq_refl => fun x1 : typD ts nil z => cast (fun x1 : Type => x1) x1
                               end (zzz e0))
                        | None => None
                      end
                  | None => fun _ : None = nth_error x u => None
                end e
              with
                | Some f => Some (f h)
                | None => None
              end =
              match typ_cast_typ ts nil x0 t with
                | Some f => Some (f (fun x1 : Type => x1) t0)
                | None => None
              end).
        intro. clearbody zzz. revert zzz.
        destruct (nth_error x u); intuition.
        inv_all. subst.
        destruct (typ_cast_typ ts nil x0 t); auto.
        f_equal. clear.
        uip_all. reflexivity. }
      { rewrite exprD'_Var.
        match goal with
          | |- context [ @eq_refl ?X ?Y ] =>
            generalize (@eq_refl X Y)
        end.
        match goal with
          | H : ?X = ?Y |- _ =>
            assert (projT1 X = projT1 Y) by (f_equal; auto)
        end.
        change (
            let zzz e := hlist_nth e u in
            forall e : nth_error x u = nth_error x u,
              match
                match
                  nth_error x u as z
                  return
                  (z = nth_error x u ->
                   option (hlist (typD ts nil) x -> typD ts nil t))
                with
                  | Some z =>
                    fun pf : Some z = nth_error x u =>
                      match typ_cast_typ ts nil z t with
                        | Some cast =>
                          Some
                            (fun e0 : hlist (typD ts nil) x =>
                               match
                                 pf in (_ = t'')
                                 return
                                 (match t'' with
                                    | Some t0 => typD ts nil t0
                                    | None => unit
                                  end -> typD ts nil t)
                               with
                                 | eq_refl => fun x0 : typD ts nil z =>
                                                cast (fun x0 : Type => x0) x0
                               end (zzz e0))
                        | None => None
                      end
                  | None => fun _ : None = nth_error x u => None
                end e
              with
                | Some f => Some (f h)
                | None => None
              end = None).
        intro; clearbody zzz.
        remember (nth_error x u).
        destruct e; auto.
        exfalso.
        rewrite split_env_projT1 in H1. simpl in *. subst.
        clear - Heqe H0.
        rewrite nth_error_map in Heqe. rewrite H0 in *. congruence.  *) admit. }
      { admit. }
    Qed.

    Theorem exprD_UVar : forall us ve u t,
      exprD us ve (UVar u) t = lookupAs us u t.
    Proof.
    Admitted.

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
      (*
      intros vs e. revert vs. induction e; simpl; intros.
      { rewrite WellTyped_expr_Var.
        rewrite exprD'_Var.
        split; intros.
        { gen_refl.
          change (
              let zzz z (pf : Some z = nth_error vs v)
                      (cast : forall F : Type -> Type, F (typD ts nil z) -> F (typD ts nil t)) :=
                  (fun e0 : hlist (typD ts nil) vs =>
                               match
                                 pf in (_ = t'')
                                 return
                                 (match t'' with
                                    | Some t0 => typD ts nil t0
                                    | None => unit
                                  end -> typD ts nil t)
                               with
                                 | eq_refl => fun x : typD ts nil z =>
                                                cast (fun x : Type => x) x
                               end (hlist_nth e0 v))
              in
              forall e : nth_error vs v = nth_error vs v,
                match
                  nth_error vs v as z
                  return
                  (z = nth_error vs v ->
                   option (hlist (typD ts nil) vs -> typD ts nil t))
                with
                  | Some z =>
                    fun pf : Some z = nth_error vs v =>
                      match typ_cast_typ ts nil z t with
                        | Some cast =>
                          Some (zzz z pf cast)
                        | None => None
                      end
                  | None => fun _ : None = nth_error vs v => None
                end e <> None
            ).
          intro zzz; clearbody zzz.
          destruct (nth_error vs v); try congruence.
          inv_all; subst. intros.
          rewrite typ_cast_typ_refl. congruence. }
        { revert H.
          gen_refl.
          change (
              let zzz z (pf : Some z = nth_error vs v)
                      (cast : forall F : Type -> Type, F (typD ts nil z) -> F (typD ts nil t)) :=
                  (fun e0 : hlist (typD ts nil) vs =>
                               match
                                 pf in (_ = t'')
                                 return
                                 (match t'' with
                                    | Some t0 => typD ts nil t0
                                    | None => unit
                                  end -> typD ts nil t)
                               with
                                 | eq_refl => fun x : typD ts nil z =>
                                                cast (fun x : Type => x) x
                               end (hlist_nth e0 v)) in
              forall e : nth_error vs v = nth_error vs v,
                match
                  nth_error vs v as z
                  return
                  (z = nth_error vs v ->
                   option (hlist (typD ts nil) vs -> typD ts nil t))
                with
                  | Some z =>
                    fun pf : Some z = nth_error vs v =>
                      match typ_cast_typ ts nil z t with
                        | Some cast =>
                          Some (zzz z pf cast)
                        | None => None
                      end
                  | None => fun _ : None = nth_error vs v => None
                end e <> None -> nth_error vs v = Some t).
          intro zzz; clearbody zzz.
          destruct (nth_error vs v); try congruence.
          intros. f_equal.
          revert H.
          match goal with
            | |- context [ match ?X with _ => _ end = _ ] =>
              consider X
          end; try congruence; intros.
          apply (typ_cast_typ_eq _ _ _ _ H). } }
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
          consider (typeof_expr (typeof_env us) vs e1); intros.
          { generalize H. generalize H0.
            eapply IHe1 in H. eapply IHe2 in H0.
            red in H; red in H0. rewrite H in H2. inv_all; subst.
            destruct t0; simpl in *; try congruence.
            change typ_eqb with (@rel_dec _ (@eq typ) _) in *.
            consider (t0_1 ?[ eq ] x0); try congruence; intros; inv_all; subst.
            destruct (exprD' us vs e1 (tyArr x0 t)); intuition.
            destruct (exprD' us vs e2 x0); intuition.
            rewrite typ_cast_typ_refl in H1; congruence. }
          { exfalso.
            eapply IHe1 in H. red in H. congruence. } }
        { consider (typeof_expr (typeof_env us) vs e1);
          try congruence; intros.
          destruct t0; try congruence.
          repeat match goal with
                   | _ : not (match ?X with _ => _ end = _) |- _ =>
                     consider X; intros
                 end; try congruence.
          generalize (typ_cast_typ_eq _ _ _ _ H2); intros.
          consider (exprD' us vs e1 (tyArr t0_1 t0_2)); intros; try congruence.
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
            consider (exprD'  us (t :: vs) e x); try congruence.
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
        rewrite nth_error_typeof_env.
        unfold lookupAs in *.
        destruct (nth_error us u).
        { split; intro.
          { destruct s. inv_all; subst. simpl in *.
            rewrite typ_cast_typ_refl. congruence. }
          { destruct s. simpl in *.
            match goal with
              | _ : not (match ?x with _ => _ end = _) |- _ =>
                consider x; intuition
            end.
            match goal with
              | _ : match ?X with _ => _ end = _ |- _ =>
                consider X; intros; try congruence
            end.
            inv_all; subst.
            f_equal; eapply (typ_cast_typ_eq _ _ _ _ H). } }
        { intuition congruence. } }
    Qed. *)
    Admitted.

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
          admit. (*
          change (
              let zzz z (pf : Some z = nth_error tvs v)
                      (cast : forall F : Type -> Type, F (typD ts nil z) -> F (typD ts nil t)) :=
                  (fun e : hlist (typD ts nil) tvs =>
                                  match
                                    pf in (_ = t'')
                                    return
                                    (match t'' with
                                       | Some t1 => typD ts nil t1
                                       | None => unit
                                     end -> typD ts nil t)
                                  with
                                    | eq_refl =>
                                      fun x : typD ts nil z => cast (fun x0 : Type => x0) x
                                  end (hlist_nth e v))
              in
              match
                     nth_error tvs v as z
                     return
                     (z = nth_error tvs v ->
                      option (hlist (typD ts nil) tvs -> typD ts nil t))
                   with
                     | Some z =>
                       fun pf : Some z = nth_error tvs v =>
                         match typ_cast_typ ts nil z t with
                           | Some cast =>
                             Some (zzz z pf cast)
                           | None => None
                         end
                     | None => fun _ : None = nth_error tvs v => None
              end eq_refl = None).
          intro zzz; clearbody zzz; revert zzz.
          rewrite H. intros.
          match goal with
            | H : ?X = _ |- match ?Y with _ => _ end = _ =>
              change Y with X; rewrite H
          end; auto. *) }
        { rewrite exprD'_Var.
          match goal with
            | |- match ?X with
                   | Some z => @?B z
                   | None => ?Y
                 end ?N = ?M =>
              change (
                  let k := B in
                  match X with
                    | Some z => k z
                    | None => Y
                  end N = M) ;
                intro k; clearbody k; revert k
          end.
          rewrite H; auto. } }
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
            rewrite exprD'_App. Cases.rewrite_all.
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
        admit. (*
        rewrite nth_error_typeof_env.
        forward; subst.
        simpl.
        rewrite exprD'_UVar. unfold lookupAs.
        rewrite H0. simpl.
        rewrite typ_cast_typ_refl.
        match goal with
          | |- match match ?X with _ => _ end with _ => _ end =
               match ?Y with _ => _ end =>
            change Y with X; destruct X
        end; auto. *) }
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
      induction tvs; simpl; intros.
      { exfalso; omega. }
      { destruct v; simpl in *.
        { repeat rewrite exprD'_Var. simpl.
          forward.
          generalize (typ_cast_typ_eq _ _ _ _ H0); intros; subst.
          rewrite typ_cast_typ_refl in H0; inv_all; subst.
          rewrite (hlist_eta vs); reflexivity. }
        { assert (v < length tvs) by omega. clear H.
          specialize (IHtvs _ H0).
          repeat rewrite exprD'_Var in *. simpl in *.
          gen_refl.
          admit. (*
          change (
              let zzz z (pf : Some z = nth_error (tvs ++ tvs') v)
                      (cast : forall F : Type -> Type, F (typD ts nil z) -> F (typD ts nil t)) :=
                  (fun e0 : hlist (typD ts nil) (tvs ++ tvs') =>
                     match
                       pf in (_ = t'')
                       return
                       (match t'' with
                          | Some t0 => typD ts nil t0
                          | None => unit
                        end -> typD ts nil t)
                     with
                       | eq_refl =>
                         fun x : typD ts nil z => cast (fun x0 : Type => x0) x
                     end (hlist_nth e0 v))
              in
              let zzz' z (pf : Some z = nth_error tvs v)
                       (cast : forall F : Type -> Type, F (typD ts nil z) -> F (typD ts nil t)) :=
                  (fun e1 : hlist (typD ts nil) tvs =>
                     match
                       pf in (_ = t'')
                       return
                       (match t'' with
                          | Some t0 => typD ts nil t0
                          | None => unit
                        end -> typD ts nil t)
                     with
                       | eq_refl =>
                         fun x : typD ts nil z => cast (fun x0 : Type => x0) x
                     end (hlist_nth e1 v))
              in
              let zzz'' z (pf : Some z = nth_error (a :: tvs) (S v))
                        (cast : forall F : Type -> Type, F (typD ts nil z) -> F (typD ts nil t)) :=
                  (fun e1 : hlist (typD ts nil) (a :: tvs) =>
                     match
                       pf in (_ = t'')
                       return
                       (match t'' with
                          | Some t0 => typD ts nil t0
                          | None => unit
                        end -> typD ts nil t)
                     with
                       | eq_refl =>
                         fun x : typD ts nil z => cast (fun x0 : Type => x0) x
                     end (hlist_nth e1 (S v)))
              in
              let zzz''' z (pf : Some z = nth_error (a :: tvs ++ tvs') (S v))
                         (cast : forall F : Type -> Type, F (typD ts nil z) -> F (typD ts nil t)) :=
                              (fun e1 : hlist (typD ts nil) (a :: tvs ++ tvs') =>
                                 match
                                   pf in (_ = t'')
                                   return
                                   (match t'' with
                                      | Some t0 => typD ts nil t0
                                      | None => unit
                                    end -> typD ts nil t)
                                 with
                                   | eq_refl =>
                                     fun x : typD ts nil z => cast (fun x0 : Type => x0) x
                                 end (hlist_nth e1 (S v)))
              in
              forall (e : nth_error tvs v = nth_error tvs v)
                     (e0 : nth_error (tvs ++ tvs') v = nth_error (tvs ++ tvs') v),
                match
                  match
                    nth_error (tvs ++ tvs') v as z
                    return
                    (z = nth_error (tvs ++ tvs') v ->
                     option (hlist (typD ts nil) (tvs ++ tvs') -> typD ts nil t))
                  with
                    | Some z =>
                      fun pf : Some z = nth_error (tvs ++ tvs') v =>
                        match typ_cast_typ ts nil z t with
                          | Some cast =>
                            Some (zzz z pf cast)
                          | None => None
                        end
                    | None => fun _ : None = nth_error (tvs ++ tvs') v => None
                  end e0
                with
                  | Some val =>
                    match
                      match
                        nth_error tvs v as z
                        return
                        (z = nth_error tvs v ->
                         option (hlist (typD ts nil) tvs -> typD ts nil t))
                      with
                        | Some z =>
                          fun pf : Some z = nth_error tvs v =>
                            match typ_cast_typ ts nil z t with
                              | Some cast =>
                                Some (zzz' z pf cast)
                              | None => None
                            end
                        | None => fun _ : None = nth_error tvs v => None
                      end e
                    with
                      | Some val' =>
                        forall (vs : hlist (typD ts nil) tvs)
                               (vs' : hlist (typD ts nil) tvs'),
                          val (hlist_app vs vs') = val' vs
                      | None => False
                    end
                  | None =>
                    match
                      match
                        nth_error tvs v as z
                        return
                        (z = nth_error tvs v ->
                         option (hlist (typD ts nil) tvs -> typD ts nil t))
                      with
                        | Some z =>
                          fun pf : Some z = nth_error tvs v =>
                            match typ_cast_typ ts nil z t with
                              | Some cast =>
                                Some (zzz' z pf cast)
                              | None => None
                            end
                        | None => fun _ : None = nth_error tvs v => None
                      end e
                    with
                      | Some _ => False
                      | None => True
                    end
                end ->
                match
                  match
                    nth_error (tvs ++ tvs') v as z
                    return
                    (z = nth_error (tvs ++ tvs') v ->
                     option (hlist (typD ts nil) (a :: tvs ++ tvs') -> typD ts nil t))
                  with
                    | Some z =>
                      fun pf : Some z = nth_error (tvs ++ tvs') v =>
                        match typ_cast_typ ts nil z t with
                          | Some cast =>
                            Some (zzz''' z pf cast)
                          | None => None
                        end
                    | None => fun _ : None = nth_error (tvs ++ tvs') v => None
                  end e0
                with
                  | Some val =>
                    match
                      match
                        nth_error tvs v as z
                        return
                        (z = nth_error tvs v ->
                         option (hlist (typD ts nil) (a :: tvs) -> typD ts nil t))
                      with
                        | Some z =>
                          fun pf : Some z = nth_error tvs v =>
                            match typ_cast_typ ts nil z t with
                              | Some cast =>
                                Some (zzz'' z pf cast)
                              | None => None
                            end
                        | None => fun _ : None = nth_error tvs v => None
                      end e
                    with
                      | Some val' =>
                        forall (vs : hlist (typD ts nil) (a :: tvs))
                               (vs' : hlist (typD ts nil) tvs'),
                          val (hlist_app vs vs') = val' vs
                      | None => False
                    end
                  | None =>
                    match
                      match
                        nth_error tvs v as z
                        return
                        (z = nth_error tvs v ->
                         option (hlist (typD ts nil) (a :: tvs) -> typD ts nil t))
                      with
                        | Some z =>
                          fun pf : Some z = nth_error tvs v =>
                            match typ_cast_typ ts nil z t with
                              | Some cast =>
                                Some (zzz'' z pf cast)
                              | None => None
                            end
                        | None => fun _ : None = nth_error tvs v => None
                      end e
                    with
                      | Some _ => False
                      | None => True
                    end
                end).
          intros zzz zzz' zzz'' zzz'''.
          assert (forall vs vs' x z pf pf' pf'' pf''' cast,
                    zzz' z pf cast vs = zzz z pf' cast (hlist_app vs vs') ->
                    zzz'' z pf'' cast (Hcons x vs) = zzz''' z pf''' cast (Hcons x (hlist_app vs vs'))).
          { subst zzz zzz' zzz'' zzz'''.
            simpl. intros.
            rewrite hlist_nth_hlist_app in *; eauto with typeclass_instances.
            rewrite hlist_nth_hlist_app in H; eauto with typeclass_instances.
            generalize (cast1 tvs tvs' v).
            generalize (cast2 tvs tvs' v).
            revert H. generalize pf; generalize pf'.
            revert pf''; revert pf'''.
            simpl.
            let z := constr:(hlist_nth vs v) in
            repeat match goal with
                     | |- context [ @hlist_nth ?A ?B ?C ?D ?E ] =>
                       change (@hlist_nth A B C D E) with z
                   end;
              generalize z.
            gen_refl. generalize (cast1 tvs tvs' v).
            generalize (cast2 tvs tvs' v).
            rewrite <- pf'. rewrite <- pf.
            uip_all'; intros.
            generalize dependent (e0 z eq_refl).
            generalize dependent (e3 z eq_refl).
            uip_all'. reflexivity. }
          { clearbody zzz; clearbody zzz'; clearbody zzz''; clearbody zzz'''.
            revert H.
            revert zzz zzz' zzz'' zzz'''.
            assert (nth_error tvs v = nth_error (tvs ++ tvs') v).
            { rewrite nth_error_app_L by auto. auto. }
            simpl.
            rewrite <- H.
            destruct (nth_error tvs v); auto.
            { intuition.
              destruct (typ_cast_typ ts nil t0 t); auto.
              intros.
              rewrite (hlist_eta vs). simpl.
              erewrite H1. reflexivity.
              symmetry. eauto. } } } } *) } }
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
      intros; repeat rewrite exprD'_Var.
      assert (length tvs <= v) by omega.
      admit.
(*
      change (
          let zzz z (pf : Some z = nth_error (tvs ++ tvs') v)
                  (cast : forall F : Type -> Type, F (typD ts nil z) -> F (typD ts nil t)) :=
              (fun e : hlist (typD ts nil) (tvs ++ tvs') =>
                 match
                   pf in (_ = t'')
                   return
                   (match t'' with
                      | Some t0 => typD ts nil t0
                      | None => unit
                    end -> typD ts nil t)
                 with
                   | eq_refl =>
                     fun x : typD ts nil z => cast (fun x0 : Type => x0) x
                 end (hlist_nth e v))
          in
          let zzz' z (pf : Some z = nth_error tvs' (v - length tvs))
                   (cast : forall F : Type -> Type, F (typD ts nil z) -> F (typD ts nil t)) :=
              (fun e : hlist (typD ts nil) tvs' =>
                 match
                   pf in (_ = t'')
                   return
                   (match t'' with
                      | Some t0 => typD ts nil t0
                      | None => unit
                    end -> typD ts nil t)
                 with
                   | eq_refl =>
                     fun x : typD ts nil z => cast (fun x0 : Type => x0) x
                 end (hlist_nth e (v - length tvs)))
          in
          match
            match
              nth_error (tvs ++ tvs') v as z
              return
              (z = nth_error (tvs ++ tvs') v ->
               option (hlist (typD ts nil) (tvs ++ tvs') -> typD ts nil t))
            with
              | Some z =>
                fun pf : Some z = nth_error (tvs ++ tvs') v =>
                  match typ_cast_typ ts nil z t with
                    | Some cast =>
                      Some (zzz z pf cast)
                    | None => None
                  end
              | None => fun _ : None = nth_error (tvs ++ tvs') v => None
            end eq_refl
          with
            | Some val =>
              match
                match
                  nth_error tvs' (v - length tvs) as z
                  return
                  (z = nth_error tvs' (v - length tvs) ->
                   option (hlist (typD ts nil) tvs' -> typD ts nil t))
                with
                  | Some z =>
                    fun pf : Some z = nth_error tvs' (v - length tvs) =>
                      match typ_cast_typ ts nil z t with
                        | Some cast =>
                          Some (zzz' z pf cast)
                        | None => None
                      end
                  | None => fun _ : None = nth_error tvs' (v - length tvs) => None
                end eq_refl
              with
                | Some val' =>
                  forall (vs : hlist (typD ts nil) tvs)
                         (vs' : hlist (typD ts nil) tvs'),
                    val (hlist_app vs vs') = val' vs'
                | None => False
              end
            | None =>
              match
                match
                  nth_error tvs' (v - length tvs) as z
                  return
                  (z = nth_error tvs' (v - length tvs) ->
                   option (hlist (typD ts nil) tvs' -> typD ts nil t))
                with
                  | Some z =>
                    fun pf : Some z = nth_error tvs' (v - length tvs) =>
                      match typ_cast_typ ts nil z t with
                        | Some cast =>
                          Some (zzz' z pf cast)
                        | None => None
                      end
                  | None => fun _ : None = nth_error tvs' (v - length tvs) => None
                end eq_refl
              with
                | Some _ => False
                | None => True
              end
          end).
      intros zzz zzz'.
      assert (forall vs vs' z pf pf' cast,
                zzz z pf cast (hlist_app vs vs') =
                zzz' z pf' cast vs').
      { subst zzz zzz'.
        simpl.
        intros; rewrite hlist_nth_hlist_app; eauto with typeclass_instances.
        generalize pf; generalize pf'.
        gen_refl.
        generalize (cast1 tvs tvs' v).
        generalize (cast2 tvs tvs' v).
        let z := constr:(hlist_nth vs' (v - length tvs)) in
            repeat match goal with
                     | |- context [ @hlist_nth ?A ?B ?C ?D ?E ] =>
                       change (@hlist_nth A B C D E) with z
                   end;
              generalize z.
        generalize (hlist_nth vs v).
        rewrite <- pf'. rewrite <- pf.
        uip_all'.
        remember (nth_error tvs v).
        destruct e1.
        { rewrite nth_error_past_end in Heqe1; congruence. }
        { generalize (e eq_refl). uip_all'.
          reflexivity. } }
      { clearbody zzz zzz'. revert zzz zzz' H1.
        rewrite nth_error_app_R by omega.
        destruct (nth_error tvs' (v - length tvs)); auto.
        intros. destruct (typ_cast_typ ts nil t0 t); auto. }
*)
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
    (*
      intros.
      generalize (@exprD'_Var_App_R (typeof_env vs') t (typeof_env vs) v).
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
      destruct (exprD' us (typeof_env vs ++ typeof_env vs') (Var v) t);
        destruct (exprD' us (typeof_env vs') (Var (v - length vs)) t); intuition.
      { rewrite X. auto. }
    Qed. *)
    Admitted.

  End with_envs.
End Build_ExprDenote.
