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

    Axiom typeof_expr_exprD : forall vs e t,
      WellTyped_expr (typeof_env us) (typeof_env vs) e t <->
      exists v, exprD us vs e t = Some v.

    Axiom typeof_expr_exprD_same_type : forall us vs e t t' v,
      exprD us vs e t = Some v ->
      typeof_expr (typeof_env us) (typeof_env vs) e = Some t' ->
      t = t'.

    Axiom exprD'_Var_App_L : forall tvs' t tvs v,
      v < length tvs ->
      match exprD' us (tvs ++ tvs') (Var v) t , exprD' us tvs (Var v) t with
        | None , None => True
        | Some val , Some val' =>
          forall vs vs',
            val (hlist_app vs vs') = val' vs
        | _ , _ => False
      end.

    Axiom exprD'_Var_App_R : forall tvs' t tvs v,
      v >= length tvs ->
      match exprD' us (tvs ++ tvs') (Var v) t , exprD' us tvs' (Var (v - length tvs)) t with
        | None , None => True
        | Some val , Some val' =>
          forall vs vs',
            val (hlist_app vs vs') = val' vs'
        | _ , _ => False
      end.

    Axiom exprD_Var_App_L : forall vs' t vs v,
      v < length vs ->
      exprD us (vs ++ vs') (Var v) t = exprD us vs (Var v) t.

    Axiom exprD_Var_App_R : forall vs' t vs v,
      v >= length vs ->
      exprD us (vs ++ vs') (Var v) t = exprD us vs' (Var (v - length vs)) t.

    Axiom exprD'_type_cast
    : forall e tvs t,
        exprD' us tvs e t =
        match typeof_expr (typeof_env us) tvs e with
          | None => None
          | Some t' =>
            match TypesI.type_cast nil t' t with
              | None => None
              | Some cast =>
                match exprD' us tvs e t' with
                  | None => None
                  | Some x =>
                    Some (fun gs => cast (fun x => x) (x gs))
                end
            end
        end.

    Axiom exprD_type_cast
    : forall e vs t,
        exprD us vs e t =
        match typeof_expr (typeof_env us) (typeof_env vs) e with
          | None => None
          | Some t' =>
            match TypesI.type_cast nil t' t with
              | None => None
              | Some cast =>
                match exprD us vs e t' with
                  | None => None
                  | Some x =>
                    Some (cast (fun x => x) x)
                end
            end
        end.

  End with_envs.

End ExprDenote.
