Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.Cases.
Require Import ExtLib.Tactics.Injection.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.ExprCore.
Require Import MirrorCore.Ext.ExprT.
Require Import MirrorCore.Ext.ExprDI.

Set Implicit Arguments.
Set Strict Implicit.

(**
 ** The denotation function with binders must be total because we
 ** can't introduce the binder until we know that we are going to get
 ** the right type out, but, at the same time, we don't know we will
 ** succeed until after we've taken the denotation of the body,
 ** which we can't do until we have the binder.
 **
 **)

Module EXPR_DENOTE_core <: ExprDenote_core.

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
        match func_lookup fs f with
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

  Lemma typeof_typeof_expr : forall e ve,
    typeof_expr (typeof_funcs fs) (typeof_env us) ve e = typeof ve e.
  Proof.
    induction e; simpl; intros;
    repeat match goal with
             | H : _ |- _ => rewrite H
           end; auto.
    { rewrite lookup_typeof_funcs.
      forward. }
    { rewrite nth_error_typeof_env. auto. }
    { change typ_eqb with (@rel_dec _ (@eq typ) _).
      destruct (typeof ve e1); auto.
      destruct (typeof ve e2); auto.
      consider (t ?[ eq ] t0); auto; intros; subst; auto.
      destruct (t ?[ eq ] t0); auto. }
    { destruct (typeof ve e); auto. destruct t; auto. }
  Qed.

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
        match func_lookup fs f with
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
            match exprD' var_env f (tvArr l r)
                , exprD' var_env x l
                , typ_cast_typ _ (fun x => x) nil r t
            with
              | Some f , Some x , Some cast =>
                Some (fun v => cast ((f v) (x v)))
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
    Proof.
      simpl. destruct u; auto.
      remember (typ_cast_typ ts (fun x : Type => x) nil u1 t).
      destruct o; auto.
      symmetry in Heqo.
      generalize (typ_cast_typ_eq ts (fun x => x) nil u1 t Heqo); intros; subst.
      rewrite typ_cast_typ_refl in Heqo.
      inv_all; subst. reflexivity.
    Qed.

    Theorem exprD'_Var : forall ve v t,
      exprD' ve (Var v) t =
      match nth_error ve v as z
            return z = nth_error ve v ->
                   option (hlist (typD ts nil) ve -> typD ts nil t)
      with
        | Some z => fun pf =>
          match typ_cast_typ _ (fun x => x) _ z t with
            | Some cast =>
              Some (fun e => match pf in _ = t''
                                   return match t'' with
                                            | Some t => typD ts nil t
                                            | None => unit
                                          end -> typD ts nil t with
                               | eq_refl => fun x => cast x
                             end (hlist_nth e v))
            | None => None
          end
        | None => fun _ => None
      end eq_refl.
    Proof.
      simpl; intros.
      match goal with
        | |- context [ @eq_refl ?X ?Y ] =>
          generalize (@eq_refl X Y)
      end.
      change (let zzz := fun e0 => hlist_nth e0 v in
              forall e : nth_error ve v = nth_error ve v,
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
           Some
             (fun e0 : hlist (typD ts nil) ve =>
              match
                pf in (_ = t'')
                return
                  (match t'' with
                   | Some t0 => typD ts nil t0
                   | None => unit
                   end -> typD ts nil t)
              with
              | eq_refl => fun x : typD ts nil t' => f x
              end (zzz e0))
       | None => None
       end
   | None => fun _ : None = nth_error ve v => None
   end e =
   match
     nth_error ve v as z
     return
       (z = nth_error ve v ->
        option (hlist (typD ts nil) ve -> typD ts nil t))
   with
   | Some z =>
       fun pf : Some z = nth_error ve v =>
       match typ_cast_typ ts (fun x : Type => x) nil z t with
       | Some cast =>
           Some
             (fun e0 : hlist (typD ts nil) ve =>
              match
                pf in (_ = t'')
                return
                  (match t'' with
                   | Some t0 => typD ts nil t0
                   | None => unit
                   end -> typD ts nil t)
              with
              | eq_refl => fun x : typD ts nil z => cast x
              end (zzz e0))
       | None => None
       end
   | None => fun _ : None = nth_error ve v => None
   end e).
      intro.
      clearbody zzz. revert zzz.
      destruct (nth_error ve v); auto.
    Qed.

    Theorem exprD'_UVar : forall ve u t,
      exprD' ve (UVar u) t =
      match lookupAs us u t with
        | Some z => Some (fun _ => z)
        | None => None
      end.
    Proof.
      reflexivity.
    Qed.

    Theorem exprD'_Func : forall ve f ts t,
      exprD' ve (Func f ts) t =
      match func_lookup fs f with
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
      destruct (func_lookup fs f); auto.
      destruct (type_apply ts (fenv f0) ts0 nil (ftype f0) (fdenote f0)); auto.
      unfold typ_cast_val.
      destruct (typ_cast_typ ts (fun x : Type => x) nil
         (instantiate_typ ts0 (ftype f0)) t); auto.
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
    Proof.
      reflexivity.
    Qed.

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
      rewrite typeof_typeof_expr. reflexivity.
    Qed.

  End with_envs.
End EXPR_DENOTE_core.
