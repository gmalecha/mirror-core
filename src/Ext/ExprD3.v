Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.Injection.
Require Import ExtLib.Tactics.EqDep.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.ExprCore.
Require Import MirrorCore.Ext.ExprDI.
Require Import MirrorCore.Ext.ExprT.

Set Implicit Arguments.
Set Strict Implicit.

Module EXPR_DENOTE_3 <: ExprDenote.

  Create HintDb exprD_rw discriminated.

  Section with_envs.
    Variable ts : types.
    Variable fs : functions ts.
    Variable us : env (typD ts).

  Fixpoint exprD_simul' (var_env : tenv typ) (e : expr) {struct e} :
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
      | Func f ts' =>
        match nth_error fs f with
          | None => None
          | Some f =>
            match type_apply _ _ ts' _ _ f.(fdenote) with
              | None => None
              | Some v =>
                Some (existT Z (instantiate_typ ts' (ftype f)) (fun _ => v))
            end
        end
      | Abs t' e =>
        match exprD_simul' (t' :: var_env) e with
          | None => None
          | Some (existT t v) =>
            Some (existT (fun t => hlist (typD ts nil) var_env -> typD ts nil t) (tvArr t' t) (fun g x => v (Hcons x g)))
        end
      | App f x =>
        match exprD_simul' var_env f with
          | None => None
          | Some (existT (tvArr l r) f) =>
            match exprD' var_env x l with
              | None => None
              | Some x => Some (existT (fun t => hlist (typD ts nil) var_env -> typD ts nil t) r (fun v => (f v) (x v)))
            end
          | _ => None
        end
      | Equal t e1 e2 =>
        match exprD' var_env e1 t , exprD' var_env e2 t with
          | Some v1, Some v2 =>
            Some (existT Z tvProp (fun v => @eq _ (v1 v) (v2 v)))
          | _ , _ => None
        end
      | Not e =>
        match exprD' var_env e tvProp with
          | None => None
          | Some P => Some (existT Z tvProp (fun v => not (P v)))
        end
    end
  with exprD' (var_env : tenv typ) (e : expr) (t : typ) {struct e} :
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
      | Func f ts' =>
        match nth_error fs f with
          | None => None
          | Some f =>
            match type_apply _ _ ts' _ _ f.(fdenote) with
              | None => None
              | Some t' =>
                match @typ_cast_val _ _ (instantiate_typ ts' (ftype f)) t t' with
                  | Some v => Some (fun _ => v)
                  | None => None
                end
            end
        end
      | Abs t' e =>
        match t as t return option (hlist (typD ts nil) var_env -> typD ts nil t)
        with
          | tvArr lt rt =>
            match typ_cast_typ ts (fun x => x) nil lt t' with
              | None => None
              | Some cast =>
                match @exprD' (lt :: var_env) e rt with
                  | None => None
                  | Some a => Some (fun x y => a (Hcons y x))
                end
            end
          | _ => None
        end
      | App f x =>
        match exprD_simul' var_env f with
          | Some (existT (tvArr l r) f) =>
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
      | Not e =>
        match t as t
              return option (hlist (typD ts nil) var_env -> typD ts nil t)
        with
          | tvProp => match exprD' var_env e tvProp with
                        | None => None
                        | Some P => Some (fun v => not (P v))
                      end
          | _ => None
        end
      | Equal t' e1 e2 =>
        match t as t return option (hlist (typD ts nil) var_env -> typD ts nil t) with
          | tvProp =>
            match exprD' var_env e1 t' , exprD' var_env e2 t' with
              | Some l , Some r =>
                Some (fun g => (l g) = (r g))
              (* equal (type := typeFor (typD := typD ts) nil t') *)
              | _ , _ => None
            end
          | _ => None
        end
    end.

  Definition exprD (var_env : env (typD ts)) (e : expr) (t : typ)
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

  Theorem exprD_Var : forall ve v t,
    exprD ve (Var v) t = lookupAs ve v t.
  Proof.
    unfold exprD; simpl; intros.
    consider (split_env ve); intros.
    unfold lookupAs.
    generalize (split_env_nth_error ve v).
    consider (nth_error ve v).
    { intros. destruct (H1 s); clear H1. clear H3. specialize (H2 eq_refl).
      rewrite H in *. simpl in *.
      destruct s; simpl in *.
      revert H2.
      change (
          let f' e0 := hlist_nth e0 v in
          match
            nth_error x v as t1
            return
            (match t1 with
               | Some v0 => typD ts nil v0
               | None => unit
             end -> Prop)
          with
            | Some v0 =>
              fun res : typD ts nil v0 =>
                existT (typD ts nil) x0 t0 = existT (typD ts nil) v0 res
            | None => fun _ : unit => False
          end (f' h) ->
          match
            match
              nth_error x v as z
              return
              (z = nth_error x v ->
               option (hlist (typD ts nil) x -> typD ts nil t))
            with
              | Some t' =>
                fun pf : Some t' = nth_error x v =>
                  match typ_cast_typ ts (fun x1 : Type => x1) nil t' t with
                    | Some f =>
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
                             | eq_refl => fun x1 : typD ts nil t' => f x1
                           end (f' e0))
                    | None => None
                  end
              | None => fun _ : None = nth_error x v => None
            end eq_refl
          with
            | Some f => Some (f h)
            | None => None
          end =
          match typ_cast_typ ts (fun x1 : Type => x1) nil x0 t with
            | Some f => Some (f t0)
            | None => None
          end).
      match goal with
        | |- context [ @eq_refl ?X ?Y ] =>
          generalize dependent (@eq_refl X Y)
      end.
      pattern (nth_error x v) at 1 5.
      destruct (nth_error x v).
      { intro.
        assert (nth_error x v = Some x0).
        { cutrewrite (x = projT1 (split_env ve)).
          rewrite split_env_projT1.
          erewrite map_nth_error. 2: eassumption. reflexivity.
          rewrite H. reflexivity. }
        { assert (x0 = t1).
          { rewrite H1 in e. inv_all; auto. }
          subst. destruct (typ_cast_typ ts (fun x => x) nil t1 t); auto.
          { intros. f_equal.
            subst f'. simpl in *. generalize dependent (hlist_nth h v).
            generalize dependent (nth_error x v).
            intros; subst.
            inv_all. f_equal; auto. } } }
      { simpl. intro. generalize dependent (hlist_nth h v).
        rewrite <- e. intuition. } }
    { intro.
      assert (nth_error x v = None).
      { cutrewrite (x = projT1 (split_env ve)).
        rewrite split_env_projT1.
        rewrite nth_error_map.
        rewrite H0. reflexivity.
        rewrite H. reflexivity. }
      { match goal with
          | |- context [ @eq_refl ?X ?Y ] =>
            generalize dependent (@eq_refl X Y)
        end.
        rewrite H; simpl. intros. clear H2.
        change (
            let f t' := fun pf : Some t' = nth_error x v =>
                    match typ_cast_typ ts (fun x0 : Type => x0) nil t' t with
                      | Some f =>
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
                               | eq_refl => fun x0 : typD ts nil t' => f x0
                             end (hlist_nth e0 v))
                      | None => None
                    end in
            match
              match
                nth_error x v as z
                return
                (z = nth_error x v ->
                 option (hlist (typD ts nil) x -> typD ts nil t))
              with
                | Some t' => f t'
                | None => fun _ : None = nth_error x v => None
              end e
            with
              | Some f => Some (f h)
              | None => None
            end = None
          ).
        intro. clearbody f.
        revert e.
        pattern (nth_error x v) at 1 3.
        rewrite H1. reflexivity. } }
  Qed.

  Theorem exprD_UVar : forall ve u t,
    exprD ve (UVar u) t = lookupAs us u t.
  Proof.
    unfold exprD. intros.
    destruct (split_env ve); simpl.
    destruct (lookupAs us u t); auto.
  Qed.

  Theorem exprD_Func : forall ve f ts t,
    exprD ve (Func f ts) t =
    match nth_error fs f with
      | None => None
      | Some f =>
        match type_apply _ _ ts _ _ f.(fdenote) with
          | None => None
          | Some t' =>
            @typ_cast_val _ _ (instantiate_typ ts (ftype f)) t t'
        end
    end.
  Proof.
    unfold exprD; intros.
    destruct (split_env ve); simpl.
    destruct (nth_error fs f); auto.
    destruct (type_apply ts (fenv f0) ts0 nil (ftype f0) (fdenote f0)); auto.
    destruct (typ_cast_val ts nil (instantiate_typ ts0 (ftype f0)) t t0); auto.
  Qed.

  Theorem exprD_Equal : forall ve t l r t',
    exprD ve (Equal t l r) t' =
    match t' as t' return option (typD ts nil t') with
      | tvProp =>
        match exprD ve l t , exprD ve r t with
          | Some l , Some r => Some (l = r)
          | _ , _ => None
        end
      | _ => None
    end.
  Proof.
    unfold exprD; intros.
    destruct (split_env ve); simpl.
    destruct t'; auto.
    destruct (exprD' x l t); destruct (exprD' x r t); auto.
  Qed.

  Theorem exprD_Not : forall ve p t',
    exprD ve (Not p) t' =
    match t' as t' return option (typD ts nil t') with
      | tvProp =>
        match exprD ve p tvProp with
          | Some p => Some (~p)
          | _ => None
        end
      | _ => None
    end.
  Proof.
    unfold exprD; intros.
    destruct (split_env ve); simpl.
    destruct t'; auto.
    destruct (exprD' x p tvProp); auto.
  Qed.

(*
   Theorem exprD_Abs_eq : forall ve t t' e val,
      exprD ve (Abs t e) t' = Some val <->
      match t' as t' return typD ts nil t' -> Prop with
        | tvArr l r => fun val =>
           match typ_cast_typ ts (fun x => x) nil l t with
             | None => False
             | Some cast =>
               forall x, exprD (existT _ t (cast x) :: ve) e r = Some (val x)
           end
        | _ => fun _ => False
      end val.
   Proof.
    unfold exprD. intros.
    destruct t'; simpl; try (destruct (split_env ve); intuition congruence).
    match goal with
      | |- (let (_,_) := _ in
            match match ?X with _ => _ end with _ => _ end) = _
           <->
           match ?Y with _ => _ end =>
        change X with Y; consider Y; intros
    end.
    { generalize (typ_cast_typ_eq _ _ _ _ _ H).
      destruct (split_env ve). intros. subst. simpl.
      destruct (exprD' (t :: x) e t'2).
      { admit. }
      { intuition try congruence.
 }
    { destruct (split_env ve). intuition congruence. }
  Qed.
*)

  (** TODO: This definition is too weak **)
   Theorem exprD_Abs : forall ve t u e val,
      exprD ve (Abs t e) (tvArr t u) = Some val ->
      forall x, exprD (existT _ t x :: ve) e u = Some (val x).
   Proof.
    unfold exprD. intros.
    change (split_env (existT (typD ts nil) t x :: ve))
      with (split_env ((existT (typD ts nil) t x :: nil) ++ ve)).
    rewrite split_env_app.
    destruct (split_env ve). simpl in *.
    rewrite typ_cast_typ_refl in *.
    destruct (exprD' (t :: x0) e u); intuition (try congruence).
    inv_all; subst. reflexivity.
  Qed.

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
     { destruct (nth_error fs f); try intuition congruence.
       destruct (type_apply ts (fenv f0) l nil (ftype f0) (fdenote f0));
         try congruence.
       inv_all. destruct H; subst. subst.
       unfold typ_cast_val. rewrite typ_cast_typ_refl. reflexivity. }
     { specialize (IHe1 ve).
       destruct (exprD_simul' ve e1); try intuition congruence.
       destruct s. specialize (IHe1 x t0 eq_refl).
       destruct x; try congruence.
       destruct (exprD' ve e2 x1); try congruence.
       inv_all. destruct H; subst. subst.
       rewrite typ_cast_typ_refl. reflexivity. }
     { specialize (IHe (t :: ve)).
       destruct (exprD_simul' (t :: ve) e); try congruence. destruct s.
       inv_all. destruct H; subst. subst.
       rewrite typ_cast_typ_refl.
       rewrite (IHe _ _ eq_refl). reflexivity. }
     { unfold lookupAs. destruct (nth_error us u); try congruence.
       destruct s. inv_all. destruct H. subst. subst.
       simpl. rewrite typ_cast_typ_refl. reflexivity. }
     { specialize (IHe1 ve). specialize (IHe2 ve).
       destruct (exprD' ve e1 t); try congruence.
       destruct (exprD' ve e2 t); try congruence.
       inv_all. destruct H. subst. subst. reflexivity. }
     { specialize (IHe ve). destruct (exprD' ve e tvProp); try congruence.
       inv_all. destruct H; subst. f_equal. auto. }
   Qed.

  Hint Rewrite exprD_Var exprD_UVar exprD_Equal exprD_Not exprD_Func : exprD_rw.

   Lemma exprD'_typeof : forall e ve t val,
     exprD' ve e t = Some val ->
     typeof_expr (typeof_funcs fs) (typeof_env us) ve e = Some t.
   Proof.
     induction e; simpl; intros.
     { admit. }
     { destruct (nth_error fs f); try congruence.
       admit. }
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
     { destruct t0; try congruence.
       specialize (IHe1 ve t). specialize (IHe2 ve t).
       destruct (exprD' ve e1 t); try congruence.
       destruct (exprD' ve e2 t); try congruence.
       erewrite IHe1 by eauto.
       erewrite IHe2 by eauto.
       change typ_eqb with (@rel_dec _ (@eq typ) _).
       rewrite rel_dec_eq_true by eauto with typeclass_instances.
       reflexivity. }
     { destruct t; try congruence.
       specialize (IHe ve tvProp).
       destruct (exprD' ve e tvProp); try congruence.
       erewrite IHe by eauto. reflexivity. }
   Qed.

   Lemma exprD'_typeof_None : forall e ve t,
     exprD' ve e t = None ->
     typeof_expr (typeof_funcs fs) (typeof_env us) ve e <> Some t.
   Proof.
     induction e; simpl; intros.
     { admit. }
     { unfold typeof_funcs. rewrite nth_error_map.
       destruct (nth_error fs f); try congruence.
       destruct f0; simpl in *.
       match goal with
         | H : match ?X with _ => _ end = _ |- _ =>
           consider X; intros
       end.
       rewrite (type_apply_length_equal' _ _ _ _ _ _ H).
       consider (EqNat.beq_nat fenv fenv); try congruence.
       match goal with
         | H : match ?X with _ => _ end = _ |- _ =>
           consider X; try congruence; intros
       end.
       intro. inv_all. subst. eapply typ_cast_val_refl; eauto.
       consider (EqNat.beq_nat (length l) fenv); try congruence; intros.
       destruct (@type_apply_length_equal ts ftype l fenv nil fdenote H1).
       clear - H H2.
       match type of H with 
         | ?T = _ =>
           match type of H2 with
             | ?T' = _ =>
               change T with T in *
           end
       end.
       rewrite H in H2. congruence. }
     { consider (exprD_simul' ve e1); intros.
       destruct s. eapply exprD'_exprD_simul' in H.
       admit. admit. }
   Admitted.

  Theorem typeof_exprD : forall vs e t,
    typeof_expr (typeof_funcs fs) (typeof_env us) (typeof_env vs) e = Some t ->
    exists val, exprD vs e t = Some val.
  Proof.
    intros vs e; revert vs.
    induction e; simpl; intros; autorewrite with exprD_rw;
      unfold lookupAs, typeof_funcs, typeof_env in *;
      repeat match goal with
               | H : _ |- _ => rewrite nth_error_map in H
               | _ : match ?X with _ => _ end = _ |- _ =>
                 (consider X; try congruence); [ intros ]
               | |- _ => progress (inv_all; subst; simpl in *)
               | H : sigT _ |- _ => destruct H
               | |- _ => rewrite typ_cast_typ_refl
               | H : forall x, _ = _ -> _ |- _ =>
                 specialize (H _ eq_refl)
               | H : forall x y, _ = _ -> _ |- _ =>
                 specialize (H _ _ eq_refl)
               | H : exists x, _ |- _ =>
                 destruct H
               | H : _ |- _ =>
                 erewrite H by eauto
             end; eauto.
  Admitted.

   Theorem exprD_App : forall ve t e arg,
      exprD ve (App e arg) t =
      match typeof_expr (typeof_funcs fs) (typeof_env us) (typeof_env ve) e with
        | Some (tvArr l r) =>
          match exprD ve e (tvArr l r) , exprD ve arg l , typ_cast_typ ts (fun x => x) nil r t with
            | Some f , Some x , Some cast =>
              Some (cast (f x))
            | _ , _ , _ => None
          end
        | _ => None
      end.
   Proof.
     unfold exprD; intros.
     unfold typeof_env in *.
     rewrite <- (split_env_projT1 ve).
     destruct (split_env ve); simpl.
     consider (exprD_simul' x e); intros.
     { destruct s.
       generalize (exprD'_exprD_simul' _ H); intro.
       generalize (exprD'_typeof _ _ H0).
       unfold typeof_env; intro; rewrite H1.
       destruct x0; auto. rewrite H0.
       destruct (exprD' x arg x0_1); auto.
       clear.
       destruct (typ_cast_typ ts (fun x0 : Type => x0) nil x0_2 t); auto. }
     { admit. }
   Qed.

  End with_envs.
End EXPR_DENOTE_3.

Import EXPR_DENOTE_3.
Export EXPR_DENOTE_3.

Instance Expr_expr ts (fs : functions ts) : Expr (typD ts) expr :=
{ exprD := exprD fs
; acc := expr_acc
; wf_acc := wf_expr_acc
}.

Create HintDb exprD_rw discriminated.
Hint Rewrite exprD_Var exprD_App exprD_UVar exprD_Equal exprD_Not exprD_Func : exprD_rw.