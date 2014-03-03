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
          match nth_error var_env x as pf
                return pf = nth_error var_env x -> option (sigT (res_type uvar_env var_env))
          with
            | None => fun _ => None
            | Some t => fun pf =>
                          Some (existT (res_type uvar_env var_env) t
                                       (fun _ e => match pf in _ = t''
                                                         return match t'' with
                                                                  | Some t => typD ts nil t
                                                                  | None => unit
                                                                end -> typD ts nil t with
                                                     | eq_refl => fun x => x
                                                   end (hlist_nth e x)))
          end eq_refl
        | UVar x =>
          match nth_error uvar_env x as pf
                return pf = nth_error uvar_env x -> option (sigT (res_type uvar_env var_env))
          with
            | None => fun _ => None
            | Some t => fun pf =>
                          Some (existT _ t (fun e _ => match pf in _ = t''
                                                             return match t'' with
                                                                      | Some t => typD ts nil t
                                                                      | None => unit
                                                                    end -> typD ts nil t with
                                                         | eq_refl => fun x => x
                                                       end (hlist_nth e x)))
          end eq_refl
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
    with exprD' (uvar_env var_env : tenv typ) (e : expr func) (t : typ) {struct e} :
           option (res_type uvar_env var_env t) :=
           match e with
             | Var x =>
               match nth_error var_env x as z
                     return z = nth_error var_env x -> option (res_type uvar_env var_env t)
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
                                                     end (hlist_nth e x))
                                  | None => None
                                end
               end eq_refl
             | UVar x =>
               match nth_error uvar_env x as z
                     return z = nth_error uvar_env x -> option (res_type uvar_env var_env t)
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
                                                     end (hlist_nth e x))
                                  | None => None
                                end
               end eq_refl
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

(*
    Definition exprD (e : expr func) (t : typ)
               (uvar_env : env (typD ts)) (var_env : env (typD ts))
    : option (typD ts nil t) :=
      let (tus,us) := split_env uvar_env in
      let (tvs,vs) := split_env var_env in
      match exprD' e t tus tvs with
        | None => None
        | Some f => Some (f us vs)
      end.
*)

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
    Proof. reflexivity. Qed.

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
         | H : context [ @eq_refl ?X ?Y ] |- _ =>
           generalize dependent (@eq_refl X Y)
       end.
       pattern (nth_error tvs v) at 1 3 7.
       destruct (nth_error tvs v); try congruence.
       intros. inv_all. subst. subst.
       rewrite typ_cast_typ_refl. reflexivity. }
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
         | H : context [ @eq_refl ?X ?Y ] |- _ =>
           generalize dependent (@eq_refl X Y)
       end.
       pattern (nth_error tus u) at 1 3 7.
       destruct (nth_error tus u); try congruence.
       intros. inv_all. subst. subst.
       rewrite typ_cast_typ_refl. reflexivity. }
   Qed.

   Lemma exprD'_typeof : forall tus e tvs t val,
     exprD' tus tvs e t = Some val ->
     typeof_expr tus tvs e = Some t.
   Proof.
     induction e; simpl; intros.
     { revert H.
       change (
           let zzz t' (pf : Some t' = nth_error tvs v)
                   (f : forall F : Type -> Type, F (typD ts nil t') -> F (typD ts nil t)) :=
               (fun _ (e : hlist (typD ts nil) tvs) =>
                          match
                            pf in (_ = t'')
                            return
                            (match t'' with
                               | Some t0 => typD ts nil t0
                               | None => unit
                             end -> typD ts nil t)
                          with
                            | eq_refl => fun x : typD ts nil t' => f (fun x : Type => x) x
                          end (hlist_nth e v))
           in
           match
             nth_error tvs v as z
             return z = nth_error tvs v -> option (res_type tus tvs t)
           with
             | Some t' =>
               fun pf : Some t' = nth_error tvs v =>
                 match typ_cast_typ ts nil t' t with
                   | Some f =>
                     Some (zzz t' pf f)
                   | None => None
                 end
             | None => fun _ : None = nth_error tvs v => None
           end eq_refl = Some val -> nth_error tvs v = Some t).
       intro zzz; clearbody zzz; revert zzz.
       gen_refl. destruct (nth_error tvs v); try congruence; intros.
       match goal with
         | _ : match ?X with _ => _ end = _ |- _ =>
           consider X; try congruence; intros
       end.
       generalize (typ_cast_typ_eq _ _ _ _ H); intros. subst; auto. }
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
     { revert H.
       change (
           let zzz t' (pf : Some t' = nth_error tus u)
                   (f : forall F : Type -> Type, F (typD ts nil t') -> F (typD ts nil t)) :=
               (fun (e : hlist (typD ts nil) tus) _ =>
                          match
                            pf in (_ = t'')
                            return
                            (match t'' with
                               | Some t0 => typD ts nil t0
                               | None => unit
                             end -> typD ts nil t)
                          with
                            | eq_refl => fun x : typD ts nil t' => f (fun x : Type => x) x
                          end (hlist_nth e u))
           in
           match
             nth_error tus u as z
             return z = nth_error tus u -> option (res_type tus tvs t)
           with
             | Some t' =>
               fun pf : Some t' = nth_error tus u =>
                 match typ_cast_typ ts nil t' t with
                   | Some f =>
                     Some (zzz t' pf f)
                   | None => None
                 end
             | None => fun _ : None = nth_error tus u => None
           end eq_refl = Some val -> nth_error tus u = Some t).
       intro zzz; clearbody zzz; revert zzz.
       gen_refl. destruct (nth_error tus u); try congruence; intros.
       match goal with
         | _ : match ?X with _ => _ end = _ |- _ =>
           consider X; try congruence; intros
       end.
       generalize (typ_cast_typ_eq _ _ _ _ H); intros. subst; auto. }
   Qed.

   Lemma exprD_simul'_None : forall e tus tvs,
     match exprD_simul' tus tvs e with
       | None => typeof_expr tus tvs e = None
       | Some t => typeof_expr tus tvs e = Some (projT1 t)
     end.
   Proof.
     induction e; simpl; intros.
     { (*change (
           let zzz t (pf : Some t = nth_error ve v) :=
               (fun e : hlist (typD ts nil) ve =>
                  match
                    pf in (_ = t'')
                    return
                    (match t'' with
                       | Some t0 => typD ts nil t0
                       | None => unit
                     end -> typD ts nil t)
                  with
                    | eq_refl => fun x : typD ts nil t => x
                  end (hlist_nth e v))
           in
           match
             match
               nth_error ve v as pf
               return
               (pf = nth_error ve v ->
                option {t : typ & hlist (typD ts nil) ve -> typD ts nil t})
             with
               | Some t =>
                 fun pf : Some t = nth_error ve v =>
                   Some
                     (existT (fun x1 : typ => hlist (typD ts nil) ve -> typD ts nil x1)
                             t
                             (zzz t pf))
               | None => fun _ : None = nth_error ve v => None
             end eq_refl
           with
             | Some t => nth_error ve v = Some (projT1 t)
             | None => nth_error ve v = None
           end).
       intro zzz; clearbody zzz; revert zzz.
       destruct (nth_error ve v); auto. *)
       admit. }
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
     { admit. }
   Qed.

   Lemma exprD'_typeof_None : forall tus e tvs t,
     exprD' tus tvs e t = None ->
     typeof_expr tus tvs e <> Some t.
   Proof.
     induction e; simpl; intros.
     { revert H. admit. (*
       change (
           let zzz t' (pf : Some t' = nth_error ve v)
                   (f : forall F : Type -> Type, F (typD ts nil t') -> F (typD ts nil t))  :=
               (fun e : hlist (typD ts nil) ve =>
              match
                pf in (_ = t'')
                return
                  (match t'' with
                   | Some t0 => typD ts nil t0
                   | None => unit
                   end -> typD ts nil t)
              with
              | eq_refl => fun x : typD ts nil t' => f (fun x : Type => x) x
              end (hlist_nth e v))
           in
           match
             nth_error ve v as z
             return
             (z = nth_error ve v ->
              option (hlist (typD ts nil) ve -> typD ts nil t))
           with
             | Some t' =>
               fun pf : Some t' = nth_error ve v =>
                 match typ_cast_typ ts nil t' t with
                   | Some f =>
                     Some (zzz t' pf f)
                   | None => None
                 end
             | None => fun _ : None = nth_error ve v => None
           end eq_refl = None -> nth_error ve v <> Some t
         ).
       intro zzz; clearbody zzz; revert zzz; gen_refl.
       destruct (nth_error ve v); try congruence; intros.
       intro. inv_all; subst.
       rewrite typ_cast_typ_refl in *. congruence. *) }
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
     { admit. (* unfold lookupAs in *.
       rewrite nth_error_typeof_env.
       destruct (nth_error us u); intuition; try congruence.
       destruct s. simpl in *; inv_all; subst.
       rewrite typ_cast_typ_refl in *. congruence. *) }
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


(**


       match goal with
         | |- context [ match ?X as z return @?R z with
                          | Some t' => fun pf : @?T t' =>
                                         match @?Y t' with
                                           | Some f => Some (@?A t' pf f)
                                           | None => @?K t'
                                         end
                          | None => ?Z
                          end ] =>
           let zzz := fresh "zzz" in
           set (zzz := A) ;
           match goal with
             | |- context C [ match ?X as z return @?R z with
                                | Some t' => fun pf : @?T t' =>
                                               match @?Y t' with
                                                 | Some f => Some (@?A t' pf f)
                                                 | None => @?K t'
                                               end
                                | None => ?Z
                              end ] =>
               idtac "a" ;
               let F := constr:(match X as z return R z with
                                       | Some t' => fun pf : T t' =>
                                                      match Y t' with
                                                        | Some f => Some (A t' pf f)
                                                        | None => K t'
                                                      end
                                       | None => Z
                                     end) in
               idtac C ;
               idtac F (*
               let res := context C[ match X as z return R z with
                                       | Some t' => fun pf : T t' =>
                                                      match Y t' with
                                                        | Some f => Some (zzz t' pf f)
                                                        | None => K t' pf
                                                      end
                                       | None => Z
                                     end ] in
               change res *)
           end
       end.
       match goal with
         | |- context C [ match ?X as z return @?R z with
                          | Some t' => fun pf : @?T t' =>
                                         match @?Y t' with
                                           | Some f => Some (@?A t' pf f)
                                           | None => @?K t' pf
                                         end
                          | None => ?Z
                          end ] =>
           let res := context C[ match X as z return R z with
                                   | Some t' => fun pf : T t' =>
                                                  match Y t' with
                                                    | Some f => Some (zzz t' pf f)
                                                    | None => K t' pf
                                                  end
                                   | None => Z
                                 end ] in
           idtac res
       end.
**)