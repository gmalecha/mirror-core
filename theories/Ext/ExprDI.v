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

Lemma nth_error_get_hlist_nth_weaken
: forall T F ls ls' n x,
    nth_error_get_hlist_nth F ls n = Some x ->
    exists z,
      nth_error_get_hlist_nth F (ls ++ ls') n =
      Some (@existT T (fun t => hlist F (ls ++ ls') -> F t) (projT1 x) z)
      /\ forall h h', projT2 x h = z (hlist_app h h').
Proof.
  intros T F ls ls'. revert ls.
  induction ls; simpl; intros; try congruence.
  { destruct n; inv_all; subst.
    { simpl. eexists; split; eauto.
      intros. rewrite (hlist_eta h). reflexivity. }
    { forward. inv_all; subst. simpl.
      apply IHls in H0. forward_reason.
      rewrite H. eexists; split; eauto.
      intros. rewrite (hlist_eta h). simpl in *.
      auto. } }
Qed.

Module Type ExprDenote_core.

  Parameter exprD' : forall {ts : types} {func : Type} {_ : RSym (typD ts) func},
    forall (tus tvs : tenv typ), expr func -> forall (t : typ),
    option (hlist (typD ts nil) tus -> hlist (typD ts nil) tvs -> typD ts nil t).

  Section with_envs.
    Variable ts : types.
    Variable func : Type.
    Variable RSym_func : RSym (typD ts) func.
    Variable tus : tenv typ.

    Axiom exprD'_Abs : forall tvs t e u,
       exprD' tus tvs (Abs t e) u =
       match u as u return option (hlist (typD ts nil) tus -> hlist (typD ts nil) tvs -> typD ts nil u) with
         | tyArr l r =>
           match typ_cast_typ _ _ l t
               , exprD' tus (t :: tvs) e r
           with
             | Some cast , Some f =>
               Some (fun u g => fun x =>
                                  f u (Hcons (F := typD ts nil)
                                             (cast (fun x => x) x) g))
             | _ , _ => None
           end
         | _ => None
       end.

    Axiom exprD'_Var : forall tvs v t,
      exprD' tus tvs (Var v) t =
      match @nth_error_get_hlist_nth _ _ tvs v with
        | None => None
        | Some (existT t' get) =>
          match typ_cast_typ ts _ t' t with
            | None => None
            | Some cast =>
              Some (fun (_ : hlist (typD ts nil) tus)
                        (vs : hlist (typD ts nil) tvs) =>
                      cast (fun x => x) (get vs))
          end
      end.

    Axiom exprD'_UVar : forall tvs u t,
      exprD' tus tvs (UVar u) t =
      match @nth_error_get_hlist_nth _ _ tus u with
        | None => None
        | Some (existT t' get) =>
          match typ_cast_typ ts _ t' t with
            | None => None
            | Some cast =>
              Some (fun (us : hlist (typD ts nil) tus)
                        (_ : hlist (typD ts nil) tvs) =>
                      cast (fun x => x) (get us))
          end
      end.

    Axiom exprD'_Sym : forall tvs f t,
      exprD' tus tvs (Inj f) t =
      match symAs f t with
        | None => None
        | Some val => Some (fun _ _ => val)
      end.

    Axiom exprD'_App : forall tvs t e arg,
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
  End with_envs.

End ExprDenote_core.

Module Type ExprDenote.
  Include ExprDenote_core.

(*
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
  Definition exprD {ts} {func : Type} {fs : RSym (typD ts) func} e t us vs
  : option (typD ts nil t) :=
    let (tus,gus) := split_env us in
    let (tvs,gvs) := split_env vs in
    match @exprD' ts func fs e t tus tvs with
      | None => None
      | Some f => Some (f gus gvs)
    end.
*)

  Section with_envs.
    Variable ts : types.
    Variable func : Type.
    Variable RSym_func : RSym (typD ts) func.

    Axiom typeof_expr_exprD' : forall tus tvs e t,
      WellTyped_expr tus tvs e t <->
      exists v, exprD' tus tvs e t = Some v.

    Variables us vs : env (typD ts).

    Instance Expr_expr : @Expr typ (typD ts) (expr func) :=
      @Build_Expr _ (typD ts) (expr func)
                  exprD'
                  _
                  (@wf_expr_acc func).

    Axiom exprD_Var : forall v t,
      exprD us vs (Var v) t = lookupAs vs v t.

    Axiom exprD_UVar : forall u t,
      exprD us vs (UVar u) t = lookupAs us u t.

    Axiom exprD_Sym : forall f t,
      exprD us vs (Inj f) t = symAs f t.

    Axiom exprD_Abs_is_arr : forall e t t',
      exprD us vs (Abs t' e) t =
      match t as t return option (typD ts nil t) with
        | tyArr l r =>
          if t' ?[ eq ] l then
            exprD us vs (Abs l e) (tyArr l r)
          else None
        | _ => None
      end.

    Axiom exprD_Abs : forall e t t' v,
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

    Axiom typeof_expr_eq_exprD_False : forall l e t,
      WellTyped_expr (typeof_env us) (l :: typeof_env vs) e t ->
      forall x, exprD us (existT _ l x :: vs) e t = None ->
                False.

    Axiom exprD_App : forall vs t e arg,
      exprD us vs (App e arg) t =
      match typeof_expr (typeof_env us) (typeof_env vs) e with
        | Some (tyArr l r) =>
          match exprD us vs e (tyArr l r)
              , exprD us vs arg l
              , typ_cast_typ _ _ r t
          with
            | Some f , Some x , Some cast =>
              Some (cast (fun x => x) (f x))
            | _ , _ , _ => None
          end
        | _ => None
      end.

    Axiom typeof_expr_exprD : forall e t,
      WellTyped_expr (typeof_env us) (typeof_env vs) e t <->
      exists v, exprD us vs e t = Some v.

    Axiom typeof_expr_exprD_same_type : forall e t t' v,
      exprD us vs e t = Some v ->
      typeof_expr (typeof_env us) (typeof_env vs) e = Some t' ->
      t = t'.

(*
    Axiom exprD'_Var_App_L : forall tus tvs' t tvs v,
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
*)

    Axiom exprD'_type_cast
    : forall tus tvs e t,
        exprD' tus tvs e t =
        match typeof_expr tus tvs e with
          | None => None
          | Some t' =>
            match TypesI.type_cast nil t' t with
              | None => None
              | Some cast =>
                match exprD' tus tvs e t' with
                  | None => None
                  | Some x =>
                    Some (fun us gs => cast (fun x => x) (x us gs))
                end
            end
        end.

    Axiom exprD_type_cast
    : forall us vs e t,
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

    Axiom exprD'_weakenU
    : forall (tus : tenv typ) (tus' : list typ)
             (tvs : tenv typ)
             (e : expr func) (t : typ)
             (val : hlist (typD ts nil) tus ->
                    hlist (typD ts nil) tvs -> typD ts nil t),
        exprD' tus tvs e t = Some val ->
        exists
          val' : hlist (typD ts nil) (tus ++ tus') ->
                 hlist (typD ts nil) tvs -> typD ts nil t,
          exprD' (tus ++ tus') tvs e t = Some val' /\
          (forall (us : hlist (typD ts nil) tus)
                  (vs : hlist (typD ts nil) tvs)
                  (us' : hlist (typD ts nil) tus'),
             val us vs = val' (hlist_app us us') vs).

    Axiom exprD'_weakenV
    : forall (tus : tenv typ)
             (tvs : tenv typ) (tvs' : list typ)
             (e : expr func) (t : typ)
             (val : hlist (typD ts nil) tus ->
                    hlist (typD ts nil) tvs -> typD ts nil t),
        exprD' tus tvs e t = Some val ->
        exists
          val' : hlist (typD ts nil) tus ->
                 hlist (typD ts nil) (tvs ++ tvs') -> typD ts nil t,
          exprD' tus (tvs ++ tvs') e t = Some val' /\
          (forall (us : hlist (typD ts nil) tus)
                  (vs : hlist (typD ts nil) tvs)
                  (vs' : hlist (typD ts nil) tvs'),
             val us vs = val' us (hlist_app vs vs')).

  End with_envs.

End ExprDenote.
