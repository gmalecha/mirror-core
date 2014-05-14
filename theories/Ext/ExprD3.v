Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.Injection.
Require Import ExtLib.Tactics.EqDep.
Require Import ExtLib.Tactics.Cases.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.ExprCore.
Require Import MirrorCore.Ext.ExprDI.
Require Import MirrorCore.Ext.ExprT.

Set Implicit Arguments.
Set Strict Implicit.

Module EXPR_DENOTE_core <: ExprDenote_core.

  Create HintDb exprD_rw discriminated.

  Section with_envs.
    Variable ts : types.
    Variable func : Type.
    Variable RSym_func : RSym (typD ts) func.

    Let res_type (tus tvs : tenv typ) (t : typ) : Type :=
      hlist (typD ts nil) tus -> hlist (typD ts nil) tvs -> typD ts nil t.

    Fixpoint exprD_simul' (uvar_env var_env : tenv typ) (e : expr func) {struct e} :
      option { t : typ & res_type uvar_env var_env t } :=
      match e return option (sigT (res_type uvar_env var_env)) with
        | Var x =>
          match @nth_error_get_hlist_nth _ _ var_env x with
            | None => None
            | Some (existT t get) =>
              Some (@existT _ (res_type uvar_env var_env) t (fun _ => get))
          end
        | UVar x =>
          match @nth_error_get_hlist_nth _ _ uvar_env x with
            | None => None
            | Some (existT t get) =>
              Some (@existT _ (res_type uvar_env var_env) t (fun x _ => get x))
          end
        | Inj f =>
          match typeof_sym f as z
                return match z with
                         | None => unit
                         | Some ft => typD ts nil ft
                       end -> _
          with
            | None => fun _ => None
            | Some ft => fun val =>
                           Some (existT (res_type uvar_env var_env)
                                        ft (fun _ _ => val))
          end (symD f)
        | Abs t' e =>
          match exprD_simul' uvar_env (t' :: var_env) e with
            | None => None
            | Some (existT t v) =>
              Some (existT (res_type uvar_env var_env)
                           (tyArr t' t) (fun u g x => v u (Hcons x g)))
          end
        | App f x =>
          match exprD_simul' uvar_env var_env f with
            | None => None
            | Some (existT (tyArr l r) f) =>
              match exprD' uvar_env var_env x l with
                | None => None
                | Some x => Some (existT (res_type uvar_env var_env) r
                                         (fun u v => (f u v) (x u v)))
              end
            | _ => None
          end
      end
    with exprD' (uvar_env var_env : tenv typ) (e : expr func) (t : typ) {struct e}
         : option (res_type uvar_env var_env t) :=
           match e with
             | Var x =>
               match @nth_error_get_hlist_nth _ _ var_env x with
                 | None => None
                 | Some (existT t' get) =>
                   match typ_cast_typ ts _ t' t with
                     | None => None
                     | Some cast =>
                       Some (fun (_ : hlist (typD ts nil) uvar_env)
                                 (vs : hlist (typD ts nil) var_env) =>
                               cast (fun x => x) (get vs))
                   end
               end
             | UVar x =>
               match @nth_error_get_hlist_nth _ _ uvar_env x with
                 | None => None
                 | Some (existT t' get) =>
                   match typ_cast_typ ts _ t' t with
                     | None => None
                     | Some cast =>
                       Some (fun (us : hlist (typD ts nil) uvar_env)
                                 (_ : hlist (typD ts nil) var_env) =>
                               cast (fun x => x) (get us))
                   end
               end
             | Inj f =>
               match symAs f t with
                 | None => None
                 | Some val => Some (fun _ _ => val)
               end
             | Abs t' e =>
               match t as t return option (res_type uvar_env var_env t)
               with
                 | tyArr lt rt =>
                   match typ_cast_typ ts nil lt t' with
                     | None => None
                     | Some cast =>
                       match @exprD' uvar_env (t' :: var_env) e rt with
                         | None => None
                         | Some a => Some (fun u x y =>
                                             a u (@Hcons _ (typD ts nil) _ _
                                                         (cast (fun x => x) y) x))
                       end
                   end
                 | _ => None
               end
             | App f x =>
               match exprD_simul' uvar_env var_env f with
                 | Some (existT (tyArr l r) f) =>
                   match exprD' uvar_env var_env x l with
                     | None => None
                     | Some x =>
                       match typ_cast_typ ts _ r t with
                         | None => None
                         | Some cast => Some (fun u v => cast (fun x => x) ((f u v) (x u v)))
                       end
                   end
                 | _ => None
               end
           end.

    Theorem split_env_nth_error : forall ve v tv,
      nth_error ve v = Some tv <->
      match nth_error (projT1 (split_env ve)) v as t
      return match t with
               | Some v => typD ts nil v
               | None => unit
             end -> Prop
      with
        | None => fun _ => False
        | Some v => fun res => tv = existT _ v res
      end (hlist_nth (projT2 (split_env ve)) v).
    Proof.
      induction ve; simpl; intros.
      { destruct v; simpl in *; intuition; inversion H. }
      { destruct v; simpl in *.
        { intuition.
          { inversion H; subst. destruct tv; reflexivity. }
          { subst. destruct a. reflexivity. } }
        { eapply IHve. } }
    Qed.
(*
    (** BOTH OF THESE PROOFS REQUIRE THE "change ..."
     ** A cleaner solution might be to export nth_error_get_hlist_nth
     ** in the interface, it seems very clean.
     **)

    Theorem exprD'_Var : forall tus tvs v t,
      exprD' tus tvs (Var v) t =
      match nth_error tvs v as z
          return z = nth_error tvs v -> option (res_type tus tvs t)
        with
          | None => fun _ => None
          | Some t' => fun pf =>
            match typ_cast_typ ts _ t' t with
              | Some f =>
                Some (fun _ e => match pf in _ = t''
                                     return match t'' with
                                              | Some t => typD ts nil t
                                              | None => unit
                                            end -> typD ts nil t with
                                 | eq_refl => fun x => f (fun x => x) x
                               end (hlist_nth e v))
              | None => None
            end
        end eq_refl.
    Proof.
      simpl. intros.
      match goal with
        | |- match ?X with _ => _ end = _ =>
          consider X; intros
      end.
      { forward.
        apply nth_error_get_hlist_nth_Some in H0. subst; simpl in *.
        destruct H0. revert H.
        gen_refl. generalize x0. }
      { apply nth_error_get_hlist_nth_None in H.
        gen_refl. }
    Qed.

    Theorem exprD'_UVar : forall tus tvs v t,
      exprD' tus tvs (UVar v) t =
      match nth_error tus v as z
          return z = nth_error tus v -> option (res_type tus tvs t)
        with
          | None => fun _ => None
          | Some t' => fun pf =>
            match typ_cast_typ ts _ t' t with
              | Some f =>
                Some (fun e _ => match pf in _ = t''
                                     return match t'' with
                                              | Some t => typD ts nil t
                                              | None => unit
                                            end -> typD ts nil t with
                                 | eq_refl => fun x => f (fun x => x) x
                               end (hlist_nth e v))
              | None => None
            end
        end eq_refl.
    Proof.
    Qed.
*)
    Theorem exprD'_Var
    : forall (tus tvs : tenv typ) (v : var) (t : typ),
        exprD' tus tvs (Var v) t =
        match nth_error_get_hlist_nth (typD ts nil) tvs v with
          | Some (existT t' get) =>
            match typ_cast_typ ts nil t' t with
              | Some cast =>
                Some
                  (fun (_ : hlist (typD ts nil) tus) (vs : hlist (typD ts nil) tvs) =>
                     cast (fun x : Type => x) (get vs))
              | None => None
            end
          | None => None
        end.
    Proof. reflexivity. Qed.

    Theorem exprD'_UVar
    : forall (tus tvs : tenv typ) (u : uvar) (t : typ),
        exprD' tus tvs (UVar u) t =
        match nth_error_get_hlist_nth (typD ts nil) tus u with
          | Some (existT t' get) =>
            match typ_cast_typ ts nil t' t with
              | Some cast =>
                Some
                  (fun (us : hlist (typD ts nil) tus) (_ : hlist (typD ts nil) tvs) =>
                     cast (fun x : Type => x) (get us))
              | None => None
            end
          | None => None
        end.
    Proof. reflexivity. Qed.

    Theorem exprD'_Abs : forall tus tvs t e u,
       exprD' tus tvs (Abs t e) u =
       match u as u return option (res_type tus tvs u) with
         | tyArr l r =>
           match typ_cast_typ _ _ l t
               , exprD' tus (t :: tvs) e r
           with
             | Some cast , Some f =>
               Some (fun u g => fun x => f u (Hcons (F := typD ts nil)
                                                    (cast (fun x => x) x) g))
             | _ , _ => None
           end
         | _ => None
       end.
    Proof. reflexivity. Qed.

    Theorem exprD'_Sym : forall tus tvs f t,
      exprD' tus tvs (@Inj func f) t =
      match symAs f t with
        | None => None
        | Some val => Some (fun _ _ => val)
      end.
    Proof. reflexivity. Qed.

   Lemma exprD'_exprD_simul' : forall tus e tvs t val,
     exprD_simul' tus tvs e = Some (@existT _ (res_type tus tvs) t val) ->
     exprD' tus tvs e t = Some val.
   Proof.
     induction e; simpl; intros.
     { match goal with
         | H : match ?X with _ => _ end = _ |- match ?Y with _ => _ end = _ =>
           change Y with X; destruct X; try congruence
       end.
       forward. subst. inv_all; subst.
       rewrite typ_cast_typ_refl. subst. reflexivity. }
     { unfold symAs.
       generalize dependent (symD f).
       destruct (typeof_sym f); try congruence; intros.
       inv_all; subst. subst. subst.
       simpl. rewrite typ_cast_typ_refl. reflexivity. }
     { unfold typ_cast_val. forward. inv_all.
       destruct H1. subst. subst.
       rewrite typ_cast_typ_refl. f_equal. }
     { specialize (IHe (t :: tvs)).
       destruct (exprD_simul' tus (t :: tvs) e); try congruence. destruct s.
       inv_all. subst. subst.
       rewrite typ_cast_typ_refl.
       rewrite (IHe _ _ eq_refl). reflexivity. }
     { match goal with
         | H : match ?X with _ => _ end = _ |- match ?Y with _ => _ end = _ =>
           change Y with X; destruct X; try congruence
       end.
       forward. subst. inv_all; subst.
       rewrite typ_cast_typ_refl. subst. reflexivity. }
   Qed.

   Lemma exprD'_typeof : forall tus e tvs t val,
     exprD' tus tvs e t = Some val ->
     typeof_expr tus tvs e = Some t.
   Proof.
     induction e; simpl; intros.
     { forward; subst; inv_all; subst.
       apply nth_error_get_hlist_nth_Some in H0.
       simpl in *.
       destruct H0; auto.
       apply typ_cast_typ_eq in H1. subst; auto. }
     { unfold symAs in *.
       generalize dependent (symD f).
       destruct (typeof_sym f); try congruence; intros.
       simpl in *.
       forward.
       generalize (typ_cast_typ_eq _ _ _ _ H); intros.
       congruence. }
     { specialize (IHe1 tvs).
       consider (exprD_simul' tus tvs e1); try congruence; intros.
       destruct s. destruct x; try congruence.
       eapply exprD'_exprD_simul' in H.
       eapply IHe1 in H. rewrite H.
       specialize (IHe2 tvs x1).
       destruct (exprD' tus tvs e2 x1); try congruence.
       specialize (IHe2 _ eq_refl). rewrite IHe2.
       simpl. change (typ_eqb x1 x1) with (x1 ?[ eq ] x1).
       rewrite rel_dec_eq_true; eauto with typeclass_instances.
       match goal with
         | H : match ?X with _ => _ end = _ |- _ =>
           consider X; intros; try congruence
       end.
       generalize (@typ_cast_typ_eq _ _ _ _ _ H0). congruence. }
     { destruct t0; try congruence.
       specialize (IHe (t :: tvs) t0_2).
       match goal with
         | H : match ?X with _ => _ end = _ |- _ =>
           consider X; intros; try congruence
       end.
       generalize (@typ_cast_typ_eq _ _ _ _ _ H); intro; subst.
       destruct (exprD' tus (t :: tvs) e t0_2); try congruence.
       erewrite IHe; eauto. }
     { forward; subst; inv_all; subst.
       apply nth_error_get_hlist_nth_Some in H0.
       simpl in *.
       destruct H0; auto.
       apply typ_cast_typ_eq in H1. subst; auto. }
   Qed.

   Lemma exprD_simul'_None : forall e tus tvs,
     match exprD_simul' tus tvs e with
       | None => typeof_expr tus tvs e = None
       | Some t => typeof_expr tus tvs e = Some (projT1 t)
     end.
   Proof.
     induction e; simpl; intros.
     { match goal with
         | |- match match ?X with _ => _ end with _ => _ end =>
           consider X; intros
       end.
       { apply nth_error_get_hlist_nth_Some in H.
         forward. subst. simpl in *. destruct H0; auto. }
       { apply nth_error_get_hlist_nth_None in H. auto. } }
     { generalize (symD f). forward. }
     { specialize (IHe1 tus tvs). specialize (IHe2 tus tvs).
       destruct (exprD_simul' tus tvs e1).
       { destruct s; simpl in *.
         rewrite IHe1.
         destruct x; simpl; try match goal with
                                  | |- context [ match ?X with _ => _ end ] =>
                                    destruct X; reflexivity
                                end.
         consider (exprD_simul' tus tvs e2); intros; try rewrite IHe2.
         { destruct s. generalize (exprD'_exprD_simul' _ H).
           consider (exprD' tus tvs e2 x1); intros.
           { simpl.
             consider (typ_eqb x1 x); auto; intros.
             eapply exprD'_typeof in H0.
             eapply exprD'_typeof in H1. congruence. }
           { simpl. consider (typ_eqb x1 x); auto; intros.
             subst. congruence. } }
         { rewrite H0.
           consider (exprD' tus tvs e2 x1); auto; intros.
           exfalso. apply exprD'_typeof in H1. congruence. } }
       { rewrite IHe1. auto. } }
     { specialize (IHe tus (t :: tvs)).
       consider (exprD_simul' tus (t :: tvs) e); intros.
       { destruct s. simpl. rewrite IHe. reflexivity. }
       { rewrite H0. auto. } }
     { match goal with
         | |- match match ?X with _ => _ end with _ => _ end =>
           consider X; intros
       end.
       { apply nth_error_get_hlist_nth_Some in H.
         forward. subst. simpl in *. destruct H0; auto. }
       { apply nth_error_get_hlist_nth_None in H. auto. } }
   Qed.

   Lemma exprD'_typeof_None : forall tus e tvs t,
     exprD' tus tvs e t = None ->
     typeof_expr tus tvs e <> Some t.
   Proof.
     induction e; simpl; intros.
     { match goal with
         | _ : match ?X with _ => _ end = _ |- _ =>
           consider X; intros
       end.
       { forward. subst.
         apply nth_error_get_hlist_nth_Some in H0.
         simpl in *. destruct H0.
         apply typ_cast_typ_neq' in H1. congruence. }
       { apply nth_error_get_hlist_nth_None in H.
         congruence. } }
     { unfold symAs in *.
       generalize dependent (symD f).
       destruct (typeof_sym f); try congruence.
       intros. intro. inv_all; subst.
       simpl in *.
       rewrite typ_cast_typ_refl in *. congruence. }
     { consider (exprD_simul' tus tvs e1); intros.
       { destruct s. eapply exprD'_exprD_simul' in H.
         rewrite (exprD'_typeof _ H).
         destruct x; simpl;
         try match goal with
               | |- context [ match ?X with _ => _ end ] =>
                 destruct X; intuition congruence
             end.
         consider (exprD' tus tvs e2 x1); intros.
         { erewrite exprD'_typeof by eauto.
           intro. consider (typ_eqb x1 x1); try congruence; intros; inv_all.
           subst. rewrite typ_cast_typ_refl in *. congruence. }
         { specialize (IHe2 _ _ H0).
           destruct (typeof_expr tus tvs e2); try congruence.
           consider (typ_eqb x1 t0); congruence. } }
       { generalize (exprD_simul'_None e1 tus tvs).
         rewrite H. intro. rewrite H1. intuition congruence. } }
     { consider (typeof_expr tus (t :: tvs) e); intros.
       2: intuition congruence.
       intro. inv_all; subst.
       rewrite typ_cast_typ_refl in *.
       specialize (IHe (t :: tvs) t1).
       destruct (exprD' tus (t :: tvs) e t1); try congruence.
       apply IHe; eauto. }
     { match goal with
         | _ : match ?X with _ => _ end = _ |- _ =>
           consider X; intros
       end.
       { forward. subst.
         apply nth_error_get_hlist_nth_Some in H0.
         simpl in *. destruct H0.
         apply typ_cast_typ_neq' in H1. congruence. }
       { apply nth_error_get_hlist_nth_None in H.
         congruence. } }
   Qed.

(*
  Theorem typeof_expr_eq_exprD_False : forall l ve e t x,
    typecheck_expr tus (l :: typeof_env ve) e t = true ->
    exprD (existT _ l x :: ve) e t = None ->
    False.
  Proof.
    intros. unfold exprD in *. simpl in *.
    consider (exprD' (l :: projT1 (split_env ve)) e t); try congruence; intros.
    eapply exprD'_typeof_None in H0.
    unfold typecheck_expr in *.
    rewrite split_env_projT1 in H0. unfold typeof_env in *.
    destruct (typeof_expr (map (projT1 (P:=typD ts nil)) us)
         (l :: map (projT1 (P:=typD ts nil)) ve) e).
    consider (Some t0 ?[ eq ] Some t); try congruence.
    simpl in *. congruence.
  Qed.
*)

  Theorem exprD'_App : forall tus tvs t e arg,
      exprD' tus tvs (App e arg) t =
      match typeof_expr tus tvs e with
        | Some (tyArr l r) =>
          match exprD' tus tvs e (tyArr l r)
              , exprD' tus tvs arg l
              , typ_cast_typ _ _ r t
          with
            | Some f , Some x , Some cast =>
              Some (fun u g => cast (fun x => x) ((f u g) (x u g)))
            | _ , _ , _ => None
          end
        | _ => None
      end.
  Proof.
    simpl; intros.
    consider (exprD_simul' tus tvs e); intros.
    { destruct s; generalize (exprD'_exprD_simul' _ H).
      intro.
      rewrite (exprD'_typeof _ H0).
      destruct x; auto.
      rewrite H0. reflexivity. }
    { generalize (exprD_simul'_None e tus tvs).
      rewrite H. intro.
      rewrite H0. auto. }
  Qed.

  End with_envs.
End EXPR_DENOTE_core.