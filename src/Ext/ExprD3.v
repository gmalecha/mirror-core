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
    Variable us : env (typD ts).

  Fixpoint exprD_simul' (var_env : tenv typ) (e : expr func) {struct e} :
    option { t : typ & hlist (typD ts nil) var_env -> typD ts nil t } :=
    let Z t := hlist (typD ts nil) var_env -> typD ts nil t in
    match e return option { t : typ & hlist (typD ts nil) var_env -> typD ts nil t } with
      | Var x =>
        match nth_error var_env x as pf
          return pf = nth_error var_env x ->
                 option { t : typ & hlist (typD ts nil) var_env -> typD ts nil t }
        with
          | None => fun _ => None
          | Some t => fun pf =>
            Some (existT _ t (fun e => match pf in _ = t''
                                           return match t'' with
                                                    | Some t => typD ts nil t
                                                    | None => unit
                                                  end -> typD ts nil t with
                                       | eq_refl => fun x => x
                                     end (hlist_nth e x)))
        end eq_refl
      | UVar x =>
        match nth_error us x with
          | None => None
          | Some (existT t v) => Some (existT Z t (fun _ => v))
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
            Some (existT (fun t => hlist (typD ts nil) var_env -> typD ts nil t)
                         ft (fun _ => val))
        end (symD f)
      | Abs t' e =>
        match exprD_simul' (t' :: var_env) e with
          | None => None
          | Some (existT t v) =>
            Some (existT (fun t => hlist (typD ts nil) var_env -> typD ts nil t)
                         (tyArr t' t) (fun g x => v (Hcons x g)))
        end
      | App f x =>
        match exprD_simul' var_env f with
          | None => None
          | Some (existT (tyArr l r) f) =>
            match exprD' var_env x l with
              | None => None
              | Some x => Some (existT (fun t => hlist (typD ts nil) var_env -> typD ts nil t) r (fun v => (f v) (x v)))
            end
          | _ => None
        end
    end
  with exprD' (var_env : tenv typ) (e : expr func) (t : typ) {struct e} :
    option (hlist (typD ts nil) var_env -> typD ts nil t) :=
    match e with
      | Var x =>
        match nth_error var_env x as z
          return z = nth_error var_env x ->
                 option (hlist (typD ts nil) var_env -> typD ts nil t)
        with
          | None => fun _ => None
          | Some t' => fun pf =>
            match typ_cast_typ ts (fun x => x) _ t' t with
              | Some f =>
                Some (fun e => match pf in _ = t''
                                     return match t'' with
                                              | Some t => typD ts nil t
                                              | None => unit
                                            end -> typD ts nil t with
                                 | eq_refl => fun x => f x
                               end (hlist_nth e x))
              | None => None
            end
        end eq_refl
      | UVar x =>
        match lookupAs us x t with
          | None => None
          | Some v => Some (fun _ => v)
        end
      | Inj f =>
        match funcAs f t with
          | None => None
          | Some val => Some (fun _ => val)
        end
      | Abs t' e =>
        match t as t return option (hlist (typD ts nil) var_env -> typD ts nil t)
        with
          | tyArr lt rt =>
            match typ_cast_typ ts (fun x => x) nil lt t' with
              | None => None
              | Some cast =>
                match @exprD' (t' :: var_env) e rt with
                  | None => None
                  | Some a => Some (fun x y => a (@Hcons _ (typD ts nil) _ _ (cast y) x))
                end
            end
          | _ => None
        end
      | App f x =>
        match exprD_simul' var_env f with
          | Some (existT (tyArr l r) f) =>
            match exprD' var_env x l with
              | None => None
              | Some x =>
                match typ_cast_typ ts (fun x => x) _ r t with
                  | None => None
                  | Some cast => Some (fun v => cast ((f v) (x v)))
                end
            end
          | _ => None
        end
    end.

  Definition exprD (var_env : env (typD ts)) (e : expr func) (t : typ)
  : option (typD ts nil t) :=
    let (ts,vs) := split_env var_env in
    match exprD' ts e t with
      | None => None
      | Some f => Some (f vs)
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

    Theorem exprD'_Var : forall ve v t,
      exprD' ve (Var v) t =
      match nth_error ve v as z
          return z = nth_error ve v ->
                 option (hlist (typD ts nil) ve -> typD ts nil t)
        with
          | None => fun _ => None
          | Some t' => fun pf =>
            match typ_cast_typ ts (fun x => x) _ t' t with
              | Some f =>
                Some (fun e => match pf in _ = t''
                                     return match t'' with
                                              | Some t => typD ts nil t
                                              | None => unit
                                            end -> typD ts nil t with
                                 | eq_refl => fun x => f x
                               end (hlist_nth e v))
              | None => None
            end
        end eq_refl.
    Proof. reflexivity. Qed.

    Theorem exprD'_Abs : forall ve t e u,
       exprD' ve (Abs t e) u =
       match u as u return option (hlist (typD ts nil) ve -> typD ts nil u) with
         | tyArr l r =>
           match typ_cast_typ _ (fun x => x) _ l t
               , exprD' (t :: ve) e r
           with
             | Some cast , Some f =>
               Some (fun g => fun x => f (Hcons (F := typD ts nil) (cast x) g))
             | _ , _ => None
           end
         | _ => None
       end.
    Proof. reflexivity. Qed.

    Theorem exprD'_UVar : forall ve u t,
      exprD' ve (UVar u) t =
      match lookupAs us u t with
        | Some z => Some (fun _ => z)
        | None => None
      end.
    Proof. reflexivity. Qed.

    Theorem exprD'_Func : forall ve f t,
      exprD' ve (@Inj func f) t =
      match funcAs f t with
        | None => None
        | Some val => Some (fun _ => val)
      end.
    Proof. reflexivity. Qed.

   Lemma exprD'_exprD_simul' : forall e ve t val,
     exprD_simul' ve e = Some (@existT _ _ t val) ->
     exprD' ve e t = Some val.
   Proof.
     induction e; simpl; intros.
     { match goal with
         | H : context [ @eq_refl ?X ?Y ] |- _ =>
           generalize dependent (@eq_refl X Y)
       end.
       pattern (nth_error ve v) at 1 3 7.
       destruct (nth_error ve v); try congruence.
       intros. inv_all. destruct H. subst. subst.
       rewrite typ_cast_typ_refl. reflexivity. }
     { unfold funcAs.
       generalize dependent (symD f).
       destruct (typeof_sym f); try congruence; intros.
       inv_all; subst. destruct H; subst. subst.
       simpl. rewrite typ_cast_typ_refl. reflexivity. }
     { unfold typ_cast_val. forward. inv_all.
       destruct H1. subst. destruct H3. subst.
       rewrite typ_cast_typ_refl. f_equal. assumption. }
     { specialize (IHe (t :: ve)).
       destruct (exprD_simul' (t :: ve) e); try congruence. destruct s.
       inv_all. destruct H; subst. subst.
       rewrite typ_cast_typ_refl.
       rewrite (IHe _ _ eq_refl). reflexivity. }
     { unfold lookupAs. destruct (nth_error us u); try congruence.
       destruct s. inv_all. destruct H. subst. subst.
       simpl. rewrite typ_cast_typ_refl. reflexivity. }
   Qed.

   Lemma exprD'_typeof : forall e ve t val,
     exprD' ve e t = Some val ->
     typeof_expr (typeof_env us) ve e = Some t.
   Proof.
     induction e; simpl; intros.
     { revert H.
       change (
           let zzz t' (pf : Some t' = nth_error ve v) f :=
               (fun e : hlist (typD ts nil) ve =>
                          match
                            pf in (_ = t'')
                            return
                            (match t'' with
                               | Some t0 => typD ts nil t0
                               | None => unit
                             end -> typD ts nil t)
                          with
                            | eq_refl => fun x : typD ts nil t' => f x
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
                 match typ_cast_typ ts (fun x : Type => x) nil t' t with
                   | Some f =>
                     Some (zzz t' pf f)
                   | None => None
                 end
             | None => fun _ : None = nth_error ve v => None
           end eq_refl = Some val -> nth_error ve v = Some t).
       intro zzz; clearbody zzz; revert zzz.
       gen_refl. destruct (nth_error ve v); try congruence; intros.
       match goal with
         | _ : match ?X with _ => _ end = _ |- _ =>
           consider X; try congruence; intros
       end.
       generalize (typ_cast_typ_eq _ _ _ _ _ H); intros. subst; auto. }
     { unfold funcAs in *.
       generalize dependent (symD f).
       destruct (typeof_sym f); try congruence; intros.
       simpl in *.
       forward.
       generalize (typ_cast_typ_eq _ _ _ _ _ H); intros.
       congruence. }
     { specialize (IHe1 ve).
       consider (exprD_simul' ve e1); try congruence; intros.
       destruct s. destruct x; try congruence.
       eapply exprD'_exprD_simul' in H.
       eapply IHe1 in H. rewrite H.
       specialize (IHe2 ve x1).
       destruct (exprD' ve e2 x1); try congruence.
       specialize (IHe2 _ eq_refl). rewrite IHe2.
       simpl. change (typ_eqb x1 x1) with (x1 ?[ eq ] x1).
       rewrite rel_dec_eq_true; eauto with typeclass_instances.
       match goal with
         | H : match ?X with _ => _ end = _ |- _ =>
           consider X; intros; try congruence
       end.
       generalize (@typ_cast_typ_eq _ _ _ _ _ _ H0). congruence. }
     { destruct t0; try congruence.
       specialize (IHe (t :: ve) t0_2).
       match goal with
         | H : match ?X with _ => _ end = _ |- _ =>
           consider X; intros; try congruence
       end.
       generalize (@typ_cast_typ_eq _ _ _ _ _ _ H); intro; subst.
       destruct (exprD' (t :: ve) e t0_2); try congruence.
       erewrite IHe; eauto. }
     { unfold lookupAs, typeof_env in *.
       rewrite nth_error_map.
       destruct (nth_error us u); try congruence.
       destruct s; simpl.
       repeat match goal with
                | H : match ?X with _ => _ end = _ |- _ =>
                  consider X; intros; try congruence
              end.
       specialize (typ_cast_typ_eq _ _ _ _  _ H). congruence. }
   Qed.

   Lemma exprD_simul'_None : forall e ve,
     match exprD_simul' ve e with
       | None => typeof_expr (typeof_env us) ve e = None
       | Some t => typeof_expr (typeof_env us) ve e = Some (projT1 t)
     end.
   Proof.
     induction e; simpl; intros.
     { change (
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
       destruct (nth_error ve v); auto. }
     { generalize (symD f). forward. }
     { specialize (IHe1 ve). specialize (IHe2 ve).
       destruct (exprD_simul' ve e1).
       { destruct s; simpl in *.
         rewrite IHe1.
         destruct x; simpl; try match goal with
                                  | |- context [ match ?X with _ => _ end ] =>
                                    destruct X; reflexivity
                                end.
         consider (exprD_simul' ve e2); intros; try rewrite IHe2.
         { destruct s. generalize (exprD'_exprD_simul' _ H).
           consider (exprD' ve e2 x1); intros.
           { simpl.
             consider (typ_eqb x1 x); auto; intros.
             eapply exprD'_typeof in H0.
             eapply exprD'_typeof in H1. congruence. }
           { simpl. consider (typ_eqb x1 x); auto; intros.
             subst. congruence. } }
         { rewrite H0.
           consider (exprD' ve e2 x1); auto; intros.
           exfalso. apply exprD'_typeof in H1. congruence. } }
       { rewrite IHe1. auto. } }
     { specialize (IHe (t :: ve)).
       consider (exprD_simul' (t :: ve) e); intros.
       { destruct s. simpl. rewrite IHe. reflexivity. }
       { rewrite H0. auto. } }
     { rewrite nth_error_typeof_env.
       destruct (nth_error us u); auto.
       destruct s. reflexivity. }
   Qed.

   Lemma exprD'_typeof_None : forall e ve t,
     exprD' ve e t = None ->
     typeof_expr (typeof_env us) ve e <> Some t.
   Proof.
     induction e; simpl; intros.
     { revert H.
       change (
           let zzz t' (pf : Some t' = nth_error ve v) f :=
               (fun e : hlist (typD ts nil) ve =>
              match
                pf in (_ = t'')
                return
                  (match t'' with
                   | Some t0 => typD ts nil t0
                   | None => unit
                   end -> typD ts nil t)
              with
              | eq_refl => fun x : typD ts nil t' => f x
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
                 match typ_cast_typ ts (fun x : Type => x) nil t' t with
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
       rewrite typ_cast_typ_refl in *. congruence. }
     { unfold funcAs in *.
       generalize dependent (symD f).
       destruct (typeof_sym f); try congruence.
       intros. intro. inv_all; subst.
       simpl in *.
       rewrite typ_cast_typ_refl in *. congruence. }
     { consider (exprD_simul' ve e1); intros.
       { destruct s. eapply exprD'_exprD_simul' in H.
         rewrite (exprD'_typeof _ _ H).
         destruct x; simpl;
         try match goal with
               | |- context [ match ?X with _ => _ end ] =>
                 destruct X; intuition congruence
             end.
         consider (exprD' ve e2 x1); intros.
         { erewrite exprD'_typeof by eauto.
           intro. consider (typ_eqb x1 x1); try congruence; intros; inv_all.
           subst. rewrite typ_cast_typ_refl in *. congruence. }
         { specialize (IHe2 _ _ H0).
           destruct (typeof_expr (typeof_env us) ve e2); try congruence.
           consider (typ_eqb x1 t1); congruence. } }
       { generalize (exprD_simul'_None e1 ve).
         rewrite H. intro. rewrite H1. intuition congruence. } }
     { consider (typeof_expr (typeof_env us) (t :: ve) e); intros.
       2: intuition congruence.
       intro. inv_all; subst.
       rewrite typ_cast_typ_refl in *.
       specialize (IHe (t :: ve) t1).
       destruct (exprD' (t :: ve) e t1); try congruence.
       apply IHe; eauto. }
     { unfold lookupAs in *.
       rewrite nth_error_typeof_env.
       destruct (nth_error us u); intuition; try congruence.
       destruct s. simpl in *; inv_all; subst.
       rewrite typ_cast_typ_refl in *. congruence. }
   Qed.

  Theorem typeof_expr_eq_exprD_False : forall l ve e t x,
    typecheck_expr (typeof_env us) (l :: typeof_env ve) e t = true ->
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

  Theorem exprD'_App : forall ve t e arg,
      exprD' ve (App e arg) t =
      match typeof_expr (typeof_env us) ve e with
        | Some (tyArr l r) =>
          match exprD' ve e (tyArr l r)
              , exprD' ve arg l
              , typ_cast_typ _ (fun x => x) _ r t
          with
            | Some f , Some x , Some cast =>
              Some (fun g => cast ((f g) (x g)))
            | _ , _ , _ => None
          end
        | _ => None
      end.
  Proof.
    simpl; intros.
    consider (exprD_simul' ve e); intros.
    { destruct s; generalize (exprD'_exprD_simul' _ H).
      intro.
      rewrite (exprD'_typeof _ _ H0).
      destruct x; auto.
      rewrite H0. reflexivity. }
    { generalize (exprD_simul'_None e ve).
      rewrite H. intro.
      rewrite H0. auto. }
  Qed.

  End with_envs.
End EXPR_DENOTE_core.

Module EXPR_DENOTE := Build_ExprDenote EXPR_DENOTE_core.


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