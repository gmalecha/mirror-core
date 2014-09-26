Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Member.
Require Import ExtLib.Data.HList.
Require Import MirrorCore.SymI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Lambda.ExprCore.

Set Implicit Arguments.
Set Strict Implicit.


(** This file contains several, alternative representations and predicates that
 ** guarantee the well-typedness of terms.
 ** Carrying these around (and manipulating them) might be expensive but they do
 ** mean that we can avoid the need to repeatedly re-typecheck terms.
 ** Their denotation functions should be simpler as well.
 **)
Section ways_to_do_terms.
  Variable typ : Type.
  Variable func : Type.
  Variable RT : RType typ.
  Variable RSym_func : RSym func.
  Variable Typ2_Fun : Typ2 _ Fun.

  (** A guaranteed well-typed expr **)
  Inductive wtexpr (tus : list (ctyp typ)) : list typ -> typ -> Type :=
  | wtVar : forall tvs t, member t tvs -> wtexpr tus tvs t
  | wtInj : forall tvs f t, typeof_sym f = Some t -> wtexpr tus tvs t
  | wtApp : forall tvs d r, wtexpr tus tvs (typ2 d r) -> wtexpr tus tvs d -> wtexpr tus tvs r
  | wtAbs : forall tvs d r, wtexpr tus (d :: tvs) r -> wtexpr tus tvs (typ2 d r)
  | wtUVar : forall tvs t, member t tus -> hlist (wtexpr tus tvs) t.(cctx) -> wtexpr tus tvs t.(vtyp).

  Section to_hlist_typ.
    Variable tus : tenv (ctyp typ).
    Variable tvs  : tenv typ.
    Variable to_wtexpr : forall t (e : expr typ func),
                           option (wtexpr tus tvs t).
    Fixpoint to_hlist_typ (ls : list (expr typ func)) (l : tenv typ)
             {struct ls}
    : option (hlist (wtexpr tus tvs) l) :=
      match l as l , ls return option (hlist (wtexpr tus tvs) l) with
        | nil , nil => Some Hnil
        | l :: ls , l' :: ls' =>
          match to_hlist_typ ls' ls
                , to_wtexpr l l'
          with
            | Some hs , Some e => Some (Hcons e hs)
            | _ , _ => None
          end
        | nil , _ :: _ => None
        | _ :: _ , nil => None
      end.
  End to_hlist_typ.

  Fixpoint to_wtexpr tus tvs t (e : expr typ func) {struct e}
  : option (wtexpr tus tvs t) :=
    match e with
      | Var v =>
        match nth_member tvs v with
          | None => None
          | Some (existT x m) =>
            match type_cast x t with
              | None => None
              | Some pf =>
                Some match pf in _ = t return wtexpr tus tvs t with
                       | eq_refl => wtVar _ m
                     end
            end
        end
      | UVar u es =>
        match nth_member tus u with
          | None => None
          | Some (existT x m) =>
            match type_cast x.(vtyp) t with
              | None => None
              | Some pf =>
                match to_hlist_typ (to_wtexpr tus tvs) es x.(cctx) with
                  | Some es =>
                    Some match pf in _ = t return wtexpr tus tvs t with
                           | eq_refl => wtUVar m es
                         end
                  | None => None
                end
            end
        end
      | Inj f =>
        match typeof_sym f as X return typeof_sym f = X -> _ with
          | None => fun _ => None
          | Some t' => fun pf =>
                         match type_cast t' t with
                           | None => None
                           | Some pf' =>
                             Some match pf' in _ = t return wtexpr tus tvs t with
                                    | eq_refl => wtInj _ _ _ pf
                                  end
                         end
        end eq_refl
      | Abs t' e =>
        typ2_match (fun _ => option _) t
                   (fun d r =>
                      match type_cast (typ2 d r) t with
                        | None => None (** DEAD CODE **)
                        | Some pf =>
                          match to_wtexpr tus (d :: tvs) r e with
                            | None => None
                            | Some e =>
                              Some match pf in _ = t return wtexpr tus tvs t with
                                     | eq_refl => wtAbs e
                                   end
                          end
                      end)
                   None
      | App f x =>
        match to_wtexpr_simul tus tvs x with
          | None => None
          | Some (existT t' x) =>
            match to_wtexpr tus tvs (typ2 t' t) f with
              | None => None
              | Some f => Some (wtApp _ f x)
            end
        end
    end
  with to_wtexpr_simul tus tvs (e : expr typ func) {struct e}
  : option { t : typ & wtexpr tus tvs t } :=
    match e with
      | Var v =>
        match nth_member tvs v with
          | None => None
          | Some (existT t m) => Some (@existT _ _ t (wtVar _ m))
        end
      | UVar u es =>
        match nth_member tus u with
          | None => None
          | Some (existT t m) =>
            match to_hlist_typ (to_wtexpr tus tvs) es t.(cctx) with
              | None => None
              | Some es => Some (@existT _ (wtexpr tus tvs) t.(vtyp) (wtUVar m es))
            end
        end
      | Inj f =>
        match typeof_sym f as X return typeof_sym f = X -> _ with
          | None => fun _ => None
          | Some t => fun pf => Some (@existT _ _ t (wtInj _ _ _ pf))
        end eq_refl
      | App a b =>
        match to_wtexpr_simul tus tvs a with
          | None => None
          | Some (existT t' a) =>
            typ2_match (fun _ => option _) t'
                       (fun d r =>
                          match to_wtexpr tus tvs d b with
                            | None => None
                            | Some b =>
                              match type_cast t' (typ2 d r) with
                                | None => None (** DEAD CODE **)
                                | Some pf =>
                                  Some (@existT _ _ r (wtApp _ match pf in _ = t return wtexpr _ _ t with
                                                                 | eq_refl => a
                                                               end
                                                             b))
                              end
                          end)
                       None
        end
      | Abs t b =>
        match to_wtexpr_simul tus (t :: tvs) b with
          | None => None
          | Some (existT t' e) => Some (@existT _ _ (typ2 t t') (wtAbs e) )
        end
    end.

  (** An expr with types decorated **)
  Inductive texpr : Type :=
  | tVar : typ -> nat -> texpr
  | tInj : typ -> func -> texpr
  | tApp : typ -> typ -> texpr -> texpr -> texpr
  | tAbs : typ -> typ -> texpr -> texpr
  | tUVar : ctyp typ -> nat -> list texpr -> texpr.

  Section to_texpr.
    Variable to_texpr : typ -> expr typ func -> option texpr.

    Fixpoint to_texpr_list (ts : tenv typ) (es : list (expr typ func)) {struct es}
    : option (list texpr) :=
      match es , ts with
        | nil , nil => Some nil
        | e :: es , t :: ts =>
          match to_texpr t e , to_texpr_list ts es with
            | Some te , Some tes => Some (te :: tes)
            | _ , _ => None
          end
        | _ , _ => None
      end.
  End to_texpr.

  Fixpoint to_texpr tus tvs t (e : expr typ func) {struct e}
  : option texpr:=
    match e with
      | Var v =>
        match nth_error tvs v with
          | None => None
          | Some t => Some (tVar t v)
        end
      | UVar u es =>
        match nth_error tus u with
          | None => None
          | Some t =>
            match to_texpr_list (to_texpr tus tvs) t.(cctx) es with
              | Some tes => Some (tUVar t u tes)
              | None => None
            end
        end
      | Inj f =>
        Some (tInj t f)
      | Abs t' e =>
        typ2_match (fun _ => option _) t
                   (fun d r =>
                      match to_texpr tus (d :: tvs) r e with
                        | None => None
                        | Some e =>
                          Some (tAbs d r e)
                      end)
                   None
      | App f x =>
        match to_texpr_simul tus tvs x with
          | None => None
          | Some (existT t' x) =>
            match to_texpr tus tvs (typ2 t' t) f with
              | None => None
              | Some f => Some (tApp t' t f x)
            end
        end
    end
  with to_texpr_simul tus tvs (e : expr typ func) {struct e}
  : option { t : typ & texpr } :=
    match e with
      | Var v =>
        match nth_error tvs v with
          | None => None
          | Some t => Some (@existT _ _ t (tVar t v))
        end
      | UVar u es =>
        match nth_error tus u with
          | None => None
          | Some t =>
            match to_texpr_list (to_texpr tus tvs) t.(cctx) es with
              | Some tes => Some (@existT _ _ t.(vtyp) (tUVar t u tes))
              | None => None
            end
        end
      | Inj f =>
        match typeof_sym f with
          | None => None
          | Some t => Some (@existT _ _ t (tInj t f))
        end
      | App a b =>
        match to_texpr_simul tus tvs a with
          | None => None
          | Some (existT t' a) =>
            typ2_match (fun _ => option _) t'
                       (fun d r =>
                          match to_texpr tus tvs d b with
                            | None => None
                            | Some b =>
                              Some (@existT _ _ r (tApp d r a b))
                          end)
                       None
        end
      | Abs t b =>
        match to_texpr_simul tus (t :: tvs) b with
          | None => None
          | Some (existT t' e) => Some (@existT _ _ (typ2 t t') (tAbs t t' e) )
        end
    end.

  Inductive hlist2 {T U : Type} (F : T -> U -> Type) : list T -> list U -> Type :=
  | Hnil2 : hlist2 F nil nil
  | Hcons2 : forall t u ts us, F t u -> hlist2 F ts us -> hlist2 F (t :: ts) (u :: us).

  Inductive WellTyped_expr (tus : list (ctyp typ))
  : list typ -> typ -> expr typ func -> Type :=
  | WT_Var : forall tvs t v, nth_error tvs v = Some t ->
                             WellTyped_expr tus tvs t (Var v)
  | WT_UVar : forall tvs t u es, nth_error tus u = Some t ->
                                 hlist2 (WellTyped_expr tus tvs) t.(cctx) es ->
                                 WellTyped_expr tus tvs t.(vtyp) (UVar u es)
  | WT_Inj : forall tvs t f, typeof_sym f = Some t ->
                             WellTyped_expr tus tvs t (Inj f)
  | WT_App : forall tvs d r f x, WellTyped_expr tus tvs (typ2 d r) f ->
                                 WellTyped_expr tus tvs d x ->
                                 WellTyped_expr tus tvs r (App f x)
  | WT_Abs : forall tvs d r e, WellTyped_expr tus (d :: tvs) r e ->
                               WellTyped_expr tus tvs (typ2 d r) (Abs d e).

  (** exprD' tus tvs e t = Some ->
   ** WellTyped_expr tus tvs t e
   **)

  Require Import ExtLib.Data.HList.

  Fixpoint exprD'_wt tus tvs t e (wt : WellTyped_expr tus tvs t e)
  : exprT tus tvs (typD t).
  refine
    match wt in WellTyped_expr _ tvs t e
          return exprT tus tvs (typD t)
    with
      | WT_Var tvs t v pf => fun _ vs =>
        match pf in _ = t return match t with
                                   | Some t => _
                                   | None => unit
                                 end with
          | eq_refl => hlist_nth vs v
        end
      | WT_UVar tvs t u es pf pf' => fun us _ =>
        match pf in _ = t return match t with
                                   | Some t => typD t.(vtyp)
                                   | None => unit
                                 end with
          | eq_refl => _ (* hlist_nth us u *)
        end
      | WT_Inj tvs t f pf => fun _ _ =>
        match pf in _ = t return match t with
                                   | Some t => typD t
                                   | None => unit
                                 end with
          | eq_refl => symD f
        end
      | WT_App tvs d r _ _ wtf wtx =>
        let f := match typ2_cast d r in _ = t return _ -> _ -> t with
                   | eq_refl => @exprD'_wt _ _ _ _ wtf
                 end in
        let x := @exprD'_wt _ _ _ _ wtx in
        fun us vs =>
          (f us vs) (x us vs)
      | WT_Abs tvs d r e wte =>
        let e := @exprD'_wt _ _ _ _ wte in
        match eq_sym (typ2_cast d r) in _ = t return _ -> _ -> t with
          | eq_refl => fun us vs x => e us (Hcons x vs)
        end
    end.
  clear. admit.
  Defined.

(*
  Lemma exprD'_exprD_wt
  : forall ts tus tvs e t wt,
    exprD' ts tus tvs e t = Some (@exprD'_wt ts tus tvs e t wt).
  Proof.
*)

End ways_to_do_terms.