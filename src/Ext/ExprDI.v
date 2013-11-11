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

Set Implicit Arguments.
Set Strict Implicit.

Module Type ExprDenote_core.

  Parameter exprD' : forall {ts : types} {func : Type} {_ : RSym (typD ts) func},
    env (typD ts) -> forall g : list typ, expr func -> forall t : typ,
    option (hlist (typD ts nil) g -> typD ts nil t).

  Section with_envs.
    Variable ts : types.
    Variable func : Type.
    Variable RSym_func : RSym (typD ts) func.
    Variable us : env (typD ts).

    Axiom exprD'_Abs : forall ve t e u,
       exprD' us ve (Abs t e) u =
       match u as u return option (hlist (typD ts nil) ve -> typD ts nil u) with
         | tyArr l r =>
           match typ_cast_typ _ _ l t
               , exprD' us (t :: ve) e r
           with
             | Some cast , Some f =>
               Some (fun g => fun x =>
                                f (Hcons (F := typD ts nil)
                                         (cast (fun x => x) x) g))
             | _ , _ => None
           end
         | _ => None
       end.

    Axiom exprD'_Var : forall ve v t,
      exprD' us ve (Var v) t =
      match nth_error ve v as z
            return z = nth_error ve v ->
                   option (hlist (typD ts nil) ve -> typD ts nil t)
      with
        | Some z => fun pf =>
          match typ_cast_typ _ _ z t with
            | Some cast =>
              Some (fun e => match pf in _ = t''
                                   return match t'' with
                                            | Some t => typD ts nil t
                                            | None => unit
                                          end -> typD ts nil t with
                               | eq_refl => fun x => cast (fun x => x) x
                             end (hlist_nth e v))
            | None => None
          end
        | None => fun _ => None
      end eq_refl.

    Axiom exprD'_UVar : forall ve u t,
      exprD' us ve (UVar u) t =
      match lookupAs us u t with
        | Some z => Some (fun _ => z)
        | None => None
      end.

    Axiom exprD'_Sym : forall ve f t,
      exprD' us ve (Inj f) t =
      match symAs f t with
        | None => None
        | Some val => Some (fun _ => val)
      end.

    Axiom exprD'_App : forall ve t e arg,
      exprD' us ve (App e arg) t =
      match typeof_expr (typeof_env us) ve e with
        | Some (tyArr l r) =>
          match exprD' us ve e (tyArr l r)
              , exprD' us ve arg l
              , typ_cast_typ _ _ r t
          with
            | Some f , Some x , Some cast =>
              Some (fun g => cast (fun x => x) ((f g) (x g)))
            | _ , _ , _ => None
          end
        | _ => None
      end.
  End with_envs.

End ExprDenote_core.

Module Type ExprDenote.
  Include ExprDenote_core.

  (**
   ** The denotation function with binders must be total because we
   ** can't introduce the binder until we know that we are going to get
   ** the right type out, but, at the same time, we don't know we will
   ** succeed until after we've taken the denotation of the body,
   ** which we can't do until we have the binder.
   **
   ** To solve this, we make precise the phase separation by returning
   ** [option (env -> typD t)] effectively allowing us to determine if
   ** there is an error before needing to get the variables.
   **
   **)
  Definition exprD {ts} {func : Type} {fs : RSym (typD ts) func} us vs e t
  : option (typD ts nil t) :=
    let (tvs,gvs) := split_env vs in
    match @exprD' ts func fs us tvs e t with
      | None => None
      | Some f => Some (f gvs)
    end.

  Section with_envs.
    Variable ts : types.
    Variable func : Type.
    Variable RSym_func : RSym (typD ts) func.
    Variable us : env (typD ts).

(*
    Axiom typeof_expr_exprD : forall vs e t,
      typeof_expr (typeof_env us) vs e = Some t ->
      exists val, exprD' us vs e t = Some val.
*)

    Axiom exprD_Var : forall ve v t,
      exprD us ve (Var v) t = lookupAs ve v t.

    Axiom exprD_UVar : forall ve u t,
      exprD us ve (UVar u) t = lookupAs us u t.

    Axiom exprD_Sym : forall ve f t,
      exprD us ve (Inj f) t = symAs f t.

    Axiom exprD_Abs_is_arr : forall vs e t t',
      exprD us vs (Abs t' e) t =
      match t as t return option (typD ts nil t) with
        | tyArr l r =>
          if t' ?[ eq ] l then
            exprD us vs (Abs l e) (tyArr l r)
          else None
        | _ => None
      end.

    Axiom exprD_Abs : forall vs e t t' v,
      exprD us vs (Abs t' e) t = Some v ->
      exists tr (pf : t = tyArr t' tr)
             (pf' : forall a : typD ts nil t', exprD us (existT (typD ts nil) _ a :: vs) e tr = None ->
                              False),
        match pf in _ = t return typD ts nil t with
          | eq_refl => v
        end = fun x => match exprD us (existT _ t' x :: vs) e tr as z
                             return (z = None -> False) -> typD ts nil tr
                       with
                         | Some x => fun _ => x
                         | None => fun pf => match pf eq_refl with end
                       end (pf' x).

    Axiom typeof_expr_eq_exprD_False : forall l ve e t,
      WellTyped_expr (typeof_env us) (l :: typeof_env ve) e t ->
      forall x, exprD us (existT _ l x :: ve) e t = None ->
                False.

    Axiom typeof_expr_exprD' : forall vs e t,
      WellTyped_expr (typeof_env us) vs e t <->
      exists v, exprD' us vs e t = Some v.

    Axiom exprD_App : forall ve t e arg,
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

  End with_envs.

End ExprDenote.

Module Build_ExprDenote (EDc : ExprDenote_core) <:
       ExprDenote with Definition exprD' := @EDc.exprD'.
  Require Import ExtLib.Tactics.Consider.
  Require Import ExtLib.Tactics.Injection.
  Require Import ExtLib.Data.ListNth.

  Include EDc.

  Definition exprD {ts} {func} {fs : RSym (typD ts) func} us vs e t
  : option (typD ts nil t) :=
    let (tvs,gvs) := split_env vs in
    match @exprD' ts _ fs us tvs e t with
      | None => None
      | Some f => Some (f gvs)
    end.

  Section with_envs.
    Variable ts : types.
    Variable func : Type.
    Variable RSym_func : RSym (typD ts) func.
    Variable us : env (typD ts).

    Theorem typeof_expr_exprD'_impl : forall vs e t,
      typeof_expr (typeof_env us) vs e = Some t ->
      exists val, exprD' us vs e t = Some val.
    Proof.
      Opaque lookup.
      intros vs e; revert vs.
      induction e; simpl; intros.
      { rewrite exprD'_Var.
        match goal with
          | |- context [ @eq_refl ?A ?B ] =>
            generalize (@eq_refl A B)
        end.
        revert H.
        generalize (nth_error vs v) at 1 2 4.
        intros. subst.
        rewrite typ_cast_typ_refl. eauto. }
      { rewrite exprD'_Sym.
        unfold symAs.
        generalize (symD f). rewrite H. intros.
        simpl.
        rewrite typ_cast_typ_refl. eauto. }
      { rewrite exprD'_App.
        specialize (IHe1 vs). specialize (IHe2 vs).
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
        specialize (IHe (t :: vs)).
        destruct (typeof_expr (typeof_env us) (t :: vs) e); try congruence.
        inv_all; subst.
        specialize (IHe _ eq_refl).
        destruct IHe.
        rewrite typ_cast_typ_refl. rewrite H. eauto. }
      { rewrite exprD'_UVar.
        unfold lookupAs.
        rewrite nth_error_typeof_env in *.
        destruct (nth_error us u); try congruence.
        inv_all; subst. destruct s; simpl.
        rewrite typ_cast_typ_refl. eauto. }
    Qed.

    Theorem exprD_Var : forall ve u t,
      exprD us ve (Var u) t = lookupAs ve u t.
    Proof.
      unfold exprD; intros.
      consider (split_env ve); intros.
      unfold lookupAs.
      consider (nth_error ve u); intros.
      { eapply split_env_nth_error in H0.
        rewrite exprD'_Var.
        rewrite H in *. simpl in *.
        destruct s.
        match goal with
          | |- context [ @eq_refl ?X ?Y ] =>
            generalize (@eq_refl X Y)
        end.
        revert H0.
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
        rewrite nth_error_map in Heqe. rewrite H0 in *. congruence. }
    Qed.

    Theorem exprD_UVar : forall ve u t,
      exprD us ve (UVar u) t = lookupAs us u t.
    Proof.
      unfold exprD; intros.
      destruct (split_env ve).
      rewrite exprD'_UVar.
      unfold lookupAs.
      consider (nth_error us u); intros; auto.
      destruct s.
      forward.
    Qed.

    Theorem exprD_Sym : forall ve f t,
      exprD us ve (Inj f) t = symAs f t.
    Proof.
      unfold exprD. intros.
      destruct (split_env ve).
      rewrite exprD'_Sym.
      forward.
    Qed.

    Theorem exprD_App : forall ve t e arg,
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
      unfold typeof_env. rewrite <- (split_env_projT1 ve).
      destruct (split_env ve).
      rewrite exprD'_App.
      simpl in *. unfold typeof_env.
      destruct (typeof_expr (map (projT1 (P:=typD ts nil)) us) x e); auto.
      destruct t0; auto.
      repeat match goal with
               | |- match match ?X with _ => _ end with _ => _ end =
                    match match ?Y with _ => _ end with _ => _ end =>
                 change X with Y; destruct Y; auto
             end.
      destruct (typ_cast_typ ts nil t0_2 t); auto.
    Qed.

    Theorem exprD_Abs_is_arr : forall vs e t t',
      exprD us vs (Abs t' e) t =
      match t as t return option (typD ts nil t) with
        | tyArr l r =>
          if t' ?[ eq ] l then
            exprD us vs (Abs l e) (tyArr l r)
          else None
        | _ => None
      end.
    Proof.
      unfold exprD. intros; destruct (split_env vs).
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

    Theorem exprD_Abs : forall vs e t t' v,
      exprD us vs (Abs t' e) t = Some v ->
      exists tr (pf : t = tyArr t' tr)
             (pf' : forall a : typD ts nil t', exprD us (existT (typD ts nil) _ a :: vs) e tr = None ->
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
      consider (split_env vs); intros.
      forward. inv_all. subst.
      rewrite exprD'_Abs in H0.
      forward. inv_all; subst.
      exists t1.
      pose proof (typ_cast_typ_eq _ _ _ _ H1); subst.
      rewrite typ_cast_typ_refl in H1. inv_all; subst.
      exists eq_refl. simpl.
      rewrite H2.
      assert (forall a : typD ts nil t', Some (t3 (Hcons a h)) = None -> False).
      congruence.
      exists H0. reflexivity.
    Qed.

    Theorem typeof_expr_eq_exprD_False : forall l ve e t,
      WellTyped_expr (typeof_env us) (l :: typeof_env ve) e t ->
      forall x, exprD us (existT _ l x :: ve) e t = None ->
                False.
    Proof.
      intros. unfold exprD in *. simpl in *.
      unfold WellTyped_expr in *.
      eapply typeof_expr_exprD'_impl in H. destruct H.
      revert H0 H.
      generalize (projT2 (split_env ve)).
      rewrite split_env_projT1.
      intros.
      match goal with
        | H : ?Y = _ , H' : match ?X with _ => _ end = _ |- _ =>
          change X with Y in * ; rewrite H in H'
      end. congruence.
    Qed.

    Lemma lem_typeof_expr_exprD' : forall vs e t,
      WellTyped_expr (typeof_env us) vs e t <->
      exprD' us vs e t <> None.
    Proof.
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
    Qed.

    Theorem typeof_expr_exprD' : forall vs e t,
      WellTyped_expr (typeof_env us) vs e t <->
      exists v, exprD' us vs e t = Some v.
    Proof.
      intros.
      rewrite lem_typeof_expr_exprD'.
      intuition.
      destruct (exprD' us vs e t); intuition. eauto.
      destruct H. congruence.
    Qed.

    Theorem typeof_expr_exprD : forall vs e t,
      WellTyped_expr (typeof_env us) (typeof_env vs) e t <->
      exists v, exprD us vs e t = Some v.
    Proof.
      intros. rewrite typeof_expr_exprD'.
      unfold exprD.
      consider (split_env vs); intros.
      assert (x = typeof_env vs).
      { clear - H. unfold typeof_env.
        rewrite <- split_env_projT1. rewrite H. reflexivity. }
      subst. intuition.
      { destruct H0.
        eexists.
        match goal with
          | H : ?X = _ |- match ?Y with _ => _ end = _ =>
            change Y with X ; rewrite H; auto
        end. }
      { destruct H0.
        match goal with
          | H : match ?X with _ => _ end = _ |- exists v, ?Y = _ =>
            change Y with X ; destruct X ; try congruence
        end. eauto. }
    Qed.

  End with_envs.
End Build_ExprDenote.
