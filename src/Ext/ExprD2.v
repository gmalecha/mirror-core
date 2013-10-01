Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.Consider.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.ExprCore.

Set Implicit Arguments.
Set Strict Implicit.


Module Type ExprDenote.

  Parameter typeof : forall (ts : types) (fs : functions ts),
    env (typD ts) -> tenv typ -> expr -> option typ.

  Parameter exprD : forall (ts : types) (fs : functions ts),
    env (typD ts) -> env (typD ts) -> expr -> forall t : typ,
    option (typD ts nil t).

  Section with_envs.
    Variable ts : types.
    Variable fs : functions ts.
    Variable us : env (typD ts).

    Axiom exprD_Var : forall ve v t,
      exprD fs us ve (Var v) t = lookupAs ve v t.

    Axiom exprD_UVar : forall ve u t,
      exprD fs us ve (UVar u) t = lookupAs us u t.

    Axiom exprD_Equal : forall ve t l r,
      exprD fs us ve (Equal t l r) tvProp =
      match exprD fs us ve l t , exprD fs us ve r t with
        | Some l , Some r => Some (l = r)
        | _ , _ => None
      end.

    Axiom exprD_Not : forall ve p,
      exprD fs us ve (Not p) tvProp =
      match exprD fs us ve p tvProp with
        | Some p => Some (~p)
        | _ => None
      end.

    Axiom exprD_Abs : forall ve t u e val,
      exprD fs us ve (Abs t e) (tvArr t u) = Some val ->
      forall x, exprD fs us (existT _ t x :: ve) e u = Some (val x).

    Axiom exprD_App : forall ve t e arg,
      exprD fs us ve (App e arg) t =
      match typeof fs us (map (@projT1 _ _) ve) e with
        | Some (tvArr l r) =>
          match exprD fs us ve e (tvArr l r) , exprD fs us ve arg l , typ_eq_odec r t with
            | Some f , Some x , Some pf =>
              match pf in _ = t
                    return option (typD ts nil t)
              with
                | eq_refl => Some (f x)
              end
            | _ , _ , _ => None
          end
        | _ => None
      end.
  End with_envs.

End ExprDenote.

(**
 ** The denotation function with binders must be total because we
 ** can't introduce the binder until we know that we are going to get
 ** the right type out, but, at the same time, we don't know we will
 ** succeed until after we've taken the denotation of the body,
 ** which we can't do until we have the binder.
 **
 **)
(** There are several potential implementations to this.
 ** (1) exprD : expr -> forall t : typ, option (typD t)
 **   suffers from the problem that since there are now a lot of
 **   [App] you do a lot of duplicate type checking.
 ** (2) exprD_simul : forall e : expr, Checked typD (typeof e)
 **   requires a more complete [typeof] function that checks
 **   all errors eagerly which can cause more work than neccessary.
 ** (3) exprD : expr -> { t : typ & ... -> typD t }
 **   this seems optimal because it avoids dependent types and
 **   will easily allow bouncing between this implementation
 **   and (1) which makes for minimal type checking and no duplicate
 **   work.
 **)

Module EXPR_DENOTE_1 <: ExprDenote.

  Section with_envs.
    Variable ts : types.
    Variable fs : functions ts.
    Variable us : env (typD ts).

  Fixpoint typeof (var_env : tenv typ) (e : expr) {struct e} : option typ :=
    match e with
      | Var x => nth_error var_env x
      | UVar x =>
        match nth_error us x with
          | None => None
          | Some tv => Some (projT1 tv)
        end
      | Func f ts =>
        match nth_error fs f with
          | None => None
          | Some r =>
          if EqNat.beq_nat (length ts) (fenv r) then
            Some (instantiate_typ ts (ftype r))
          else
            None
        end
      | App e e' =>
        Monad.bind (typeof var_env e) (fun ft =>
        Monad.bind (typeof var_env e') (fun xt =>
        type_of_apply ft xt))
      | Abs t e =>
        match typeof (t :: var_env) e with
          | None => None
          | Some t' => Some (tvArr t t')
        end
      | Equal t e1 e2 =>
        match typeof var_env e1 with
          | None => None
          | Some t' => match typeof var_env e2 with
                         | None => None
                         | Some t'' => if t ?[ eq ] t' then
                                         if t' ?[ eq ] t'' then Some tvProp
                                         else None
                                       else None
                       end
        end
      | Not e =>
        match typeof var_env e with
          | None => None
          | Some tvProp => Some tvProp
          | Some _ => None
        end
    end.

  Fixpoint exprD' (var_env : tenv typ) (e : expr) (t : typ) {struct e} :
    option (hlist (typD ts nil) var_env -> typD ts nil t) :=
    match e as e return option (hlist (typD ts nil) var_env -> typD ts nil t) with
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
                match @typ_cast_val _ nil (instantiate_typ ts' (ftype f)) t t' with
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
        match typeof var_env f with
          | Some (tvArr l r) =>
            match exprD' var_env f (tvArr l r) , exprD' var_env x l , typ_eq_odec r t with
              | Some f , Some x , Some pf =>
                match pf in _ = t
                      return option (hlist (typD ts nil) var_env -> typD ts nil t)
                with
                  | eq_refl => Some (fun v => (f v) (x v))
                end
              | _ , _ , _ => None
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
      | Not e =>
        match t as t return option (hlist (typD ts nil) var_env -> typD ts nil t)
 with
          | tvProp =>
            match exprD' var_env e tvProp with
              | Some P => Some (fun g => not (P g))
              | _ => None
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

  Axiom exprD_Var : forall ve v t,
      exprD ve (Var v) t = lookupAs ve v t.

    Axiom exprD_UVar : forall ve u t,
      exprD ve (UVar u) t = lookupAs us u t.

    Axiom exprD_Equal : forall ve t l r,
      exprD ve (Equal t l r) tvProp =
      match exprD ve l t , exprD ve r t with
        | Some l , Some r => Some (l = r)
        | _ , _ => None
      end.

    Axiom exprD_Not : forall ve p,
      exprD ve (Not p) tvProp =
      match exprD ve p tvProp with
        | Some p => Some (~p)
        | _ => None
      end.

    Axiom exprD_Abs : forall ve t u e val,
      exprD ve (Abs t e) (tvArr t u) = Some val ->
      forall x, exprD (existT _ t x :: ve) e u = Some (val x).

    Axiom exprD_App : forall ve t e arg,
      exprD ve (App e arg) t =
      match typeof (map (@projT1 _ _) ve) e with
        | Some (tvArr l r) =>
          match exprD ve e (tvArr l r) , exprD ve arg l , typ_eq_odec r t with
            | Some f , Some x , Some pf =>
              match pf in _ = t
                    return option (typD ts nil t)
              with
                | eq_refl => Some (f x)
              end
            | _ , _ , _ => None
          end
        | _ => None
      end.
  End with_envs.
End EXPR_DENOTE_1.

Module EXPR_DENOTE_3 <: ExprDenote.

  Section with_envs.
    Variable ts : types.
    Variable fs : functions ts.
    Variable us : env (typD ts).

    Fixpoint typeof (var_env : tenv typ) (e : expr) {struct e} : option typ :=
    match e with
      | Var x => nth_error var_env x
      | UVar x =>
        match nth_error us x with
          | None => None
          | Some tv => Some (projT1 tv)
        end
      | Func f ts =>
        match nth_error fs f with
          | None => None
          | Some r =>
          if EqNat.beq_nat (length ts) (fenv r) then
            Some (instantiate_typ ts (ftype r))
          else
            None
        end
      | App e e' =>
        Monad.bind (typeof var_env e) (fun ft =>
        Monad.bind (typeof var_env e') (fun xt =>
        type_of_apply ft xt))
      | Abs t e =>
        match typeof (t :: var_env) e with
          | None => None
          | Some t' => Some (tvArr t t')
        end
      | Equal t e1 e2 => Some tvProp
      | Not e => Some tvProp
    end.

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

Require Import ExtLib.Tactics.Injection.
  Require Import ExtLib.Tactics.EqDep.
  Require Import ExtLib.Data.ListNth.


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

  Theorem exprD_Equal : forall ve t l r,
    exprD ve (Equal t l r) tvProp =
    match exprD ve l t , exprD ve r t with
      | Some l , Some r => Some (l = r)
      | _ , _ => None
    end.
  Proof.
    unfold exprD; intros.
    destruct (split_env ve); simpl.
    destruct (exprD' x l t); destruct (exprD' x r t); auto.
  Qed.

  Theorem exprD_Not : forall ve p,
    exprD ve (Not p) tvProp =
    match exprD ve p tvProp with
      | Some p => Some (~p)
      | _ => None
    end.
  Proof.
    unfold exprD; intros.
    destruct (split_env ve); simpl.
    destruct (exprD' x p tvProp); auto.
  Qed.

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

   Theorem exprD_App : forall ve t e arg,
      exprD ve (App e arg) t =
      match typeof (map (@projT1 _ _) ve) e with
        | Some (tvArr l r) =>
          match exprD ve e (tvArr l r) , exprD ve arg l , typ_eq_odec r t with
            | Some f , Some x , Some pf =>
              match pf in _ = t
                    return option (typD ts nil t)
              with
                | eq_refl => Some (f x)
              end
            | _ , _ , _ => None
          end
        | _ => None
      end.
   Proof.
     unfold exprD; intros.
    destruct (split_env ve); simpl.
    rewrite <- split_env_projT1.
   Admitted.

  End with_envs.
End EXPR_DENOTE_3.

Module EXPR_DENOTE_2 <: ExprDenote.
  Require Import ExtLib.Data.Checked.

  Section with_envs.
    Variable ts : types.
    Variable fs : functions ts.
    Variable us : env (typD ts).

    Definition todo : forall T : Type, T. Admitted.


    Definition rapply te (ft xt : typ) :
    Checked (fun t => typD ts te ft -> typD ts te xt -> typD ts te t)
            (type_of_apply ft xt) :=
    match ft as ft
          return Checked (fun t => typD ts te ft -> typD ts te xt -> typD ts te t)
                         (type_of_apply ft xt)
    with
      | tvArr l r =>
        match typ_eqb l xt as e
              return typ_eqb l xt = e ->
                     Checked (fun t => typD ts te (tvArr l r) -> typD ts te xt -> typD ts te t)
                             (if e then Some r else None)
        with
          | true => fun pf =>
            @Success _ _ _  (fun f x => f (match eq_sym (typ_eqb_true _ _ pf) in _ = t
                                                 return typD ts te t
                                           with
                                             | eq_refl => x
                                           end))
          | false => fun _ => Failure _
        end eq_refl
      | _ => Failure _
    end.

Fixpoint typeof (var_env : tenv typ) (e : expr) {struct e} : option typ :=
    match e with
      | Var x => nth_error var_env x
      | UVar x =>
        match nth_error us x with
          | None => None
          | Some tv => Some (projT1 tv)
        end
      | Func f ts =>
        match nth_error fs f with
          | None => None
          | Some r =>
          if EqNat.beq_nat (length ts) (fenv r) then
            Some (instantiate_typ ts (ftype r))
          else
            None
        end
      | App e e' =>
        Monad.bind (typeof var_env e) (fun ft =>
        Monad.bind (typeof var_env e') (fun xt =>
        type_of_apply ft xt))
      | Abs t e =>
        match typeof (t :: var_env) e with
          | None => None
          | Some t' => Some (tvArr t t')
        end
      | Equal t e1 e2 =>
        match typeof var_env e1 with
          | None => None
          | Some t' => match typeof var_env e2 with
                         | None => None
                         | Some t'' => if t ?[ eq ] t' then
                                         if t' ?[ eq ] t'' then Some tvProp
                                         else None
                                       else None
                       end
        end
      | Not e =>
        match typeof var_env e with
          | None => None
          | Some tvProp => Some tvProp
          | Some _ => None
        end
    end.

  Fixpoint exprD_simul' (var_env : tenv typ) (e : expr) {struct e} :
    Checked (fun t => hlist (typD ts nil) var_env -> typD ts nil t)
            (typeof var_env e) :=
    let Z := (fun t => hlist (typD ts nil) var_env -> typD ts nil t) in
    match e as e
      return Checked Z (typeof var_env e)
    with
      | Var x =>
        match nth_error var_env x as z
          return z = nth_error var_env x -> Checked Z z
        with
          | None => fun _ => Failure _
          | Some t => fun pf =>
            @Success _ Z
                     t (fun e => match pf in _ = t''
                                     return match t'' with
                                              | Some t => typD ts nil t
                                              | None => unit
                                            end -> typD ts nil t with
                                 | eq_refl => fun x => x
                               end (hlist_nth e x))
        end eq_refl
      | UVar x =>
        match nth_error us x as tv
              return Checked (fun t : typ => hlist (typD ts nil) var_env -> typD ts nil t)
                             (match tv with
                                | None => None
                                | Some tv => Some (projT1 tv)
                              end)
        with
          | None => Failure _
          | Some t =>
            @Success _ Z
                     (projT1 t) (fun _ : hlist (typD ts nil) var_env => projT2 t)
        end
      | Func f ts' => todo _
(*
        match nth_error funcs f as ft
              return Checked (fun t : typ => hlist (typD ts nil) var_env -> typD ts nil t)
                             (match ft with
                                | None => None
                                | Some r => Some (instantiate_typ ts' (ftype r))
                              end)
        with
          | None => Failure _
          | Some f =>
            match type_apply _ _ ts' _ _ f.(fdenote) with
              | None => Failure _
              | Some v =>
                @Success _ Z
                         (instantiate_typ ts' (ftype f)) (fun _ => v)
            end
        end *)
      | Abs t' e =>
        match @exprD_simul' (t' :: var_env) e in Checked _ tc
              return Checked Z
                             (match tc with
                                | None => None
                                | Some t'' => Some (tvArr t' t'')
                              end)
        with
          | Failure => Failure _
          | Success t v => @Success _ (fun t => hlist (typD ts nil) var_env ->
                                       typD ts nil t)
                                    (tvArr t' t)
                                    (fun g => fun x => v (Hcons x g))
        end
      | App f x =>
        match exprD_simul' var_env f in Checked _ tc
              return Checked Z
                             (match tc with
                                | None => None
                                | Some tf => match typeof var_env x with
                                                | None => None
                                                | Some tx => type_of_apply tf tx
                                             end
                              end)
        with
          | Failure => Failure _
          | Success tf f =>
            match exprD_simul' var_env x in Checked _ tc
                  return Checked Z
                                 (match tc with
                                    | None => None
                                    | Some tx => type_of_apply tf tx
                                  end)
            with
              | Failure => Failure _
              | Success tx x =>
                match rapply nil tf tx with
                  | Failure => Failure _
                  | Success t ap =>
                    @Success _ Z
                             t (fun v => ap (f v) (x v))
                end
            end
        end
      | Equal t e1 e2 =>
        match exprD_simul' var_env e1 in Checked _ tc
              return Checked Z
                             (match tc with
                                | None => None
                                | Some t' =>
                                  match typeof var_env e2 with
                                    | None => None
                                    | Some t'' => if t ?[ eq ] t' then
                                                    if t' ?[ eq ] t'' then Some tvProp
                                                    else None
                                                  else None
                                  end
                              end)
        with
          | Failure => Failure _
          | Success t1 v1 =>
            match exprD_simul' var_env e2 in Checked _ tc
                  return Checked Z
                                 (match tc with
                                      | None => None
                                      | Some t'' => if t ?[ eq ] t1 then
                                                      if t1 ?[ eq ] t'' then Some tvProp
                                                      else None
                                                    else None
                                  end)
            with
              | Failure => Failure _
              | Success t2 v2 =>
                match t ?[ eq ] t1 as res
                      return Checked Z
                                 (if res then
                                    if t1 ?[ eq ] t2 then Some tvProp
                                    else None
                                  else None)
                with
                  | false => Failure _
                  | true =>
                    match t1 ?[ eq ] t2 as res
                          return t1 ?[ eq ] t2 = res ->
                                 Checked Z
                                         (if res then Some tvProp else None)
                    with
                      | false => fun _ => Failure _
                      | true => fun pf =>
                                  match ((proj1 (rel_dec_correct _ _)) pf) in _ = t
                                        return (hlist (typD ts nil) var_env -> typD ts nil t) ->
                                               Checked Z
                                                       (Some tvProp)
                                  with
                                    | eq_refl => fun v2 =>
                                      @Success _ Z
                                               tvProp (fun v => @eq _ (v1 v) (v2 v))
                                  end v2
                    end eq_refl
                end
            end
        end
      | Not e =>
        match exprD_simul' var_env e in Checked _ tc
              return Checked Z
                             match tc with
                               | Some tvProp => Some tvProp
                               | _ => None
                             end
        with
          | Failure => Failure _
          | Success tvProp P =>
            @Success _ Z
                     tvProp (fun g => not (P g))
          | Success _ _ => Failure _
        end
    end.

  Definition exprD (var_env : env (typD ts)) (e : expr) (t : typ)
  : option (typD ts nil t) :=
    let (ts',vs) := split_env var_env in
    match exprD_simul' ts' e with
      | Success t' v =>
        @typ_cast_val ts nil  t' t (v vs)
      | Failure => None
    end.


    Axiom exprD_Var : forall ve v t,
      exprD ve (Var v) t = lookupAs ve v t.

    Axiom exprD_UVar : forall ve u t,
      exprD ve (UVar u) t = lookupAs us u t.

    Axiom exprD_Equal : forall ve t l r,
      exprD ve (Equal t l r) tvProp =
      match exprD ve l t , exprD ve r t with
        | Some l , Some r => Some (l = r)
        | _ , _ => None
      end.

    Axiom exprD_Not : forall ve p,
      exprD ve (Not p) tvProp =
      match exprD ve p tvProp with
        | Some p => Some (~p)
        | _ => None
      end.

    Axiom exprD_Abs : forall ve t u e val,
      exprD ve (Abs t e) (tvArr t u) = Some val ->
      forall x, exprD (existT _ t x :: ve) e u = Some (val x).

    Axiom exprD_App : forall ve t e arg,
      exprD ve (App e arg) t =
      match typeof (map (@projT1 _ _) ve) e with
        | Some (tvArr l r) =>
          match exprD ve e (tvArr l r) , exprD ve arg l , typ_eq_odec r t with
            | Some f , Some x , Some pf =>
              match pf in _ = t
                    return option (typD ts nil t)
              with
                | eq_refl => Some (f x)
              end
            | _ , _ , _ => None
          end
        | _ => None
      end.

  End with_envs.
End EXPR_DENOTE_2.
