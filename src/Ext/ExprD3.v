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

Module EXPR_DENOTE_core <: ExprDenote_core.

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
                match @exprD' (t' :: var_env) e rt with
                  | None => None
                  | Some a => Some (fun x y => a (@Hcons _ (typD ts nil) _ _ (cast y) x))
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
         | tvArr l r =>
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

    Theorem exprD'_Func : forall ve f ts t,
      exprD' ve (Func f ts) t =
      match nth_error fs f with
        | None => None
        | Some f =>
          match type_apply _ _ ts _ _ f.(fdenote) with
            | None => None
            | Some t' =>
              match @typ_cast_typ _ (fun x => x) _ (instantiate_typ ts (ftype f)) t with
                | None => None
                | Some cast => Some (fun _ => cast t')
              end
          end
      end.
    Proof.
      simpl; intros.
      destruct (nth_error fs f); auto.
      destruct (type_apply ts (fenv f0) ts0 nil (ftype f0) (fdenote f0)); auto.
      unfold typ_cast_val.
      destruct (typ_cast_typ ts (fun x => x) nil (instantiate_typ ts0 (ftype f0))); auto.
    Qed.

    Theorem exprD'_Equal : forall ve t l r t',
      exprD' ve (Equal t l r) t' =
      match t' as t' return option (hlist (typD ts nil) ve -> typD ts nil t') with
        | tvProp =>
          match exprD' ve l t , exprD' ve r t with
            | Some l , Some r => Some (fun g => l g = r g)
            | _ , _ => None
          end
        | _ => None
      end.
    Proof. reflexivity. Qed.

    Theorem exprD'_Not : forall ve p t',
      exprD' ve (Not p) t' =
      match t' as t' return option (hlist (typD ts nil) ve -> typD ts nil t') with
        | tvProp =>
          match exprD' ve p tvProp with
            | Some p => Some (fun g => not (p g))
            | _ => None
          end
        | _ => None
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

   Lemma exprD'_typeof : forall e ve t val,
     exprD' ve e t = Some val ->
     typeof_expr (typeof_funcs fs) (typeof_env us) ve e = Some t.
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
     { rewrite nth_error_typeof_funcs.
       destruct (nth_error fs f); try congruence.
       destruct f0; simpl in *. unfold typ_cast_val in *.
       repeat match goal with
                | _ : match ?X with _ => _ end = _ |- _ =>
                  consider X; try congruence; intros
              end.
       generalize (typ_cast_typ_eq _ _ _ _ _ H0); intros; subst.
       inv_all; subst.
       rewrite (type_apply_length_equal' _ _ _ _ _ _ H).
       consider (EqNat.beq_nat fenv fenv); congruence. }
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

   Lemma exprD_simul'_None : forall e ve,
     match exprD_simul' ve e with
       | None => typeof_expr (typeof_funcs fs) (typeof_env us) ve e = None
       | Some t => typeof_expr (typeof_funcs fs) (typeof_env us) ve e = Some (projT1 t)
     end.
   Proof.
     induction e; simpl; intros.
     {

       change (
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
     { rewrite nth_error_typeof_funcs.
       destruct (nth_error fs f); try congruence.
       destruct f0; simpl in *.
       match goal with
         | |- match match ?X with _ => _ end with _ => _ end =>
           consider X; intros
       end.
       { simpl. consider (EqNat.beq_nat (length l) fenv); auto.
         generalize (type_apply_length_equal' _ _ _ _ _ _ H).
         congruence. }
       { consider (EqNat.beq_nat (length l) fenv); auto.
         intros; subst.
         exfalso.
         destruct (@type_apply_length_equal ts ftype l (length l) nil fdenote eq_refl).
         match type of H with
           | ?X = _ =>
             match type of H0 with
               | ?Y = _ =>
                 change X with Y in * ; rewrite H in H0 ; congruence
             end
         end. } }
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
     { specialize (IHe1 ve); specialize (IHe2 ve).
       repeat match goal with
                | _ : match ?X with _ => _ end |- _ =>
                  consider X; intros
                | H : sigT _ |- _ => destruct H
                | H : _ |- _ =>
                  rewrite H || rewrite (exprD'_exprD_simul' _ H)
              end; simpl in *.
       { consider (typ_eqb t x); intros; subst.
         { generalize (exprD'_exprD_simul' _ H).
           generalize (exprD'_exprD_simul' _ H0).
           intros. rewrite H1.
           rewrite rel_dec_eq_true; eauto with typeclass_instances.
           consider (x ?[ eq ] x0); intros; subst.
           { rewrite H2. auto. }
           { consider (exprD' ve e2 x); auto; intros.
             generalize (exprD'_typeof _ _ H2).
             generalize (exprD'_typeof _ _ H4).
             congruence. } }
         { consider (exprD' ve e1 t); intros; auto.
           exfalso.
           eapply exprD'_typeof in H2. congruence.
           rewrite rel_dec_neq_false; eauto with typeclass_instances. } }
       { consider (exprD' ve e1 t); auto; intros.
         eapply exprD'_typeof in H2. congruence. }
       { consider (exprD' ve e2 t); intros.
         { eapply exprD'_typeof in H2; congruence. }
         { destruct (t ?[ eq ] x); destruct (exprD' ve e1 t); auto. } }
       { consider (exprD' ve e1 t); auto; intros.
         eapply exprD'_typeof in H3. congruence. } }
     { specialize (IHe ve).
       consider (exprD_simul' ve e); intros.
       { rewrite IHe. destruct s; simpl in *.
         destruct x; try rewrite (exprD'_exprD_simul' _ H); auto;
         consider (exprD' ve e tvProp); auto; intros;
         eapply exprD'_typeof in H0; try congruence. }
       { rewrite H0.
         consider (exprD' ve e tvProp); auto; intros.
         eapply exprD'_typeof in H1. congruence. } }
   Qed.

   Lemma exprD'_typeof_None : forall e ve t,
     exprD' ve e t = None ->
     typeof_expr (typeof_funcs fs) (typeof_env us) ve e <> Some t.
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
           destruct (typeof_expr (typeof_funcs fs) (typeof_env us) ve e2); try congruence.
           consider (typ_eqb x1 t1); congruence. } }
       { generalize (exprD_simul'_None e1 ve).
         rewrite H. intro. rewrite H1. intuition congruence. } }
     { consider (typeof_expr (typeof_funcs fs) (typeof_env us) (t :: ve) e); intros.
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
     { intro.
       repeat match goal with
                | _ : match ?X with _ => _ end = _ |- _ =>
                  (consider X; try congruence); [ subst; intros ]
              end.
       subst.
       consider (exprD' ve e1 t); intros.
       consider (exprD' ve e2 t); intros.
       congruence.
       eapply IHe2; eauto.
       eapply IHe1; eauto. }
     { intro.
       repeat match goal with
                | _ : match ?X with _ => _ end = _ |- _ =>
                  (consider X; try congruence); [ subst; intros ]
              end.
       subst.
       eapply IHe; eauto. }
   Qed.

  Theorem typeof_expr_eq_exprD_False : forall l ve e t x,
    typecheck_expr (typeof_funcs fs) (typeof_env us) (l :: typeof_env ve) e t = true ->
    exprD (existT _ l x :: ve) e t = None ->
    False.
  Proof.
    intros. unfold exprD in *. simpl in *.
    consider (exprD' (l :: projT1 (split_env ve)) e t); try congruence; intros.
    eapply exprD'_typeof_None in H0.
    unfold typecheck_expr in *.
    rewrite split_env_projT1 in H0. unfold typeof_env in *.
    destruct (typeof_expr (typeof_funcs fs) (map (projT1 (P:=typD ts nil)) us)
         (l :: map (projT1 (P:=typD ts nil)) ve) e).
    consider (Some t0 ?[ eq ] Some t); try congruence.
    simpl in *. congruence.
  Qed.

  Theorem exprD'_App : forall ve t e arg,
      exprD' ve (App e arg) t =
      match typeof_expr (typeof_funcs fs) (typeof_env us) ve e with
        | Some (tvArr l r) =>
          match exprD' ve e (tvArr l r)
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