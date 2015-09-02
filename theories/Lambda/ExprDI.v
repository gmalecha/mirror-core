Require Import ExtLib.Data.HList.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.AbsAppI.
Require Import MirrorCore.Lambda.ExprCore.

Set Implicit Arguments.
Set Strict Implicit.

Module Type ExprDenote.

  Section with_types.
    Context {typ : Type}.
    Context {func : Type}.
    Context {RType_typD : RType typ}.
    Context {Typ2_Fun : Typ2 RType_typD RFun}.
    Context {RSym_func : RSym func}.

    (** Reasoning principles **)
    Context {RTypeOk_typD : @RTypeOk _ _}.
    Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.
    Context {RSymOk_func : RSymOk RSym_func}.

    Let typ_arr : typ -> typ -> typ := @typ2 _ _ _ _.
    Let arr_match := @typ2_match _ _ _ _.
    Let typD_arr
    : forall a b, typD (typ_arr a b) = (typD a -> typD b)
      := @typ2_cast _ _ _ _.

    Definition Rcast T {a b} (pf : Rty a b) : T (typD a) -> T (typD b) :=
      Relim T (Rsym pf).

    Definition Rcast_val
    : forall {a b} (pf : Rty a b), typD a -> typD b :=
      @Rcast (fun T => T).

    Parameter exprD'
    : forall {Typ2_Fun : Typ2 _ RFun}
             {RSym_func : RSym func}
             (tus tvs : tenv typ) (t : typ) (e : expr typ func),
        option (exprT tus tvs (typD t)).

    Axiom exprD'_respects
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall tus tvs t t' e (pf : Rty t' t),
        exprD' tus tvs t e =
        Rcast (fun T => option (exprT tus tvs T)) pf (exprD' tus tvs t' e).

    Section typeof_expr.
      Variable tus : tenv typ.

      Definition type_of_apply (tv x : typ) : option typ :=
        arr_match (fun _ => option typ) tv
                  (fun d r =>
                     match type_cast d x with
                       | Some _ => Some r
                       | None => None
                     end)
                  None.

      Fixpoint typeof_expr (tvs : tenv typ) (e : expr typ func)
      : option typ :=
        match e with
        | Var x  => nth_error tvs x
        | UVar x => nth_error tus x
        | Inj f => typeof_sym f
        | App e e' =>
          match typeof_expr tvs e
              , typeof_expr tvs e'
          with
            | Some tf , Some tx =>
              type_of_apply tf tx
            | _ , _ => None
          end
        | Abs t e =>
          match typeof_expr (t :: tvs) e with
            | None => None
            | Some t' => Some (typ_arr t t')
          end
      end.
    End typeof_expr.

    Axiom exprD'_Var
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall tus tvs t v,
        exprD' tus tvs t (Var v) =
        match nth_error_get_hlist_nth typD tvs v with
        | Some (existT _ t' get) =>
          match type_cast t' t with
          | Some cast => Some (fun us vs => Rcast_val cast (get vs))
          | _ => None
          end
        | _ => None
        end.

    Axiom exprD'_UVar
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall tus tvs t u,
        exprD' tus tvs t (UVar u) =
        match nth_error_get_hlist_nth typD tus u with
        | Some (existT _ t' get) =>
          match type_cast t' t with
          | Some cast => Some (fun us vs => Rcast_val cast (get us))
          | _ => None
          end
        | _ => None
        end.

    Axiom exprD'_Inj
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall tus tvs t s,
        exprD' tus tvs t (Inj s) =
        match symAs s t with
        | Some val => Some (fun _ _ => val)
        | None => None
        end.

    Axiom exprD'_App
    : RTypeOk (typ:=typ) -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall tus tvs t f x,
        exprD' tus tvs t (App f x) =
        match typeof_expr tus tvs x with
        | Some t' =>
          match exprD' tus tvs (typ_arr t' t) f
              , exprD' tus tvs t' x
          with
          | Some f , Some x => Some (exprT_App f x)
          | _ , _ => None
          end
        | None => None
        end.

    Axiom exprD'_Abs
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall tus tvs t t' e,
        exprD' tus tvs t (Abs t' e) =
        arr_match (fun T => option (exprT tus tvs T)) t
                  (fun d r =>
                     match type_cast d t' with
                     | Some cast =>
                       match exprD' tus (t' :: tvs) r e with
                       | Some val => Some (fun us vs x =>
                                             val us (Hcons (Rcast_val cast x) vs))
                       | None => None
                       end
                     | None => None
                     end)
                  None.

  End with_types.

End ExprDenote.

Module Type ExprFacts (ED : ExprDenote).

  Section with_types.
    Context {typ : Type}.
    Context {RType_typD : RType typ}.
    Context {Typ2_Fun : Typ2 _ RFun}.
    Context {func : Type}.
    Context {RSym_func : RSym func}.

    (** Reasoning principles **)
    Context {RTypeOk_typD : RTypeOk}.
    Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.
    Context {RSymOk_func : RSymOk RSym_func}.

    Axiom exprD'_ind
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall (P : forall tus tvs, _ -> forall t, option (exprT tus tvs (typD t)) -> Prop) tus
        (Hnone : forall tus tvs e t,
                   ED.exprD' tus tvs t e = None -> P tus tvs e t None)
        (Hvar : forall tvs v t t' get (pf : Rty t t'),
                  nth_error_get_hlist_nth _ tvs v = Some (@existT _ _ t' get) ->
                  P tus tvs (Var v) t
                    (Some (Relim (exprT tus tvs) pf (fun _ (vs : hlist _ tvs) => get vs))))
        (Huvar : forall tvs u t t' get (pf : Rty t t'),
                   nth_error_get_hlist_nth _ tus u = Some (@existT _ _ t' get) ->
                   P tus tvs (UVar u) t
                     (Some (Relim (exprT tus tvs) pf ((fun us _ => get us)))))
        (Hinj : forall tvs i t t' (pf : typeof_sym i = Some t)
                (pf' : Rty t' t),
                  P tus tvs (Inj i) t'
                    (Some (Relim (exprT tus tvs) pf' (fun _ _ =>
                             (match pf in _ = t
                                    return match t with
                                             | Some t => typD t
                                             | None => unit
                                           end with
                                | eq_refl => symD i
                              end)))))
        (Happ : forall tvs d r f x fval xval,
                  ED.typeof_expr tus tvs x = Some d ->
                  P tus tvs f (typ2 d r) (Some fval) ->
                  P tus tvs x d (Some xval) ->
                  P tus tvs (App f x) r
                    (Some (exprT_App fval xval)))
        (Habs : forall tvs d r e fval,
                  P tus (d :: tvs) e r (Some fval) ->
                  P tus tvs (Abs d e) (typ2 d r) (Some (exprT_Abs fval))),
        forall tvs e t,
        P tus tvs e t (ED.exprD' tus tvs t e).

    Axiom typeof_expr_weaken
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall tus tvs e t tus' tvs',
        ED.typeof_expr tus tvs e = Some t ->
        ED.typeof_expr (tus ++ tus') (tvs ++ tvs') e = Some t.

    Axiom exprD'_weaken
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall tus tvs (e : expr typ func) t val tus' tvs',
        ED.exprD' tus tvs t e = Some val ->
        exists val',
          ED.exprD' (tus ++ tus') (tvs ++ tvs') t e = Some val' /\
          forall us vs us' vs',
            val us vs = val' (hlist_app us us') (hlist_app vs vs').

    Axiom exprD'_type_cast
    : @RTypeOk typ _ -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall tus tvs e t,
        ED.exprD' tus tvs t e =
        match ED.typeof_expr (Typ2_Fun:=Typ2_Fun) tus tvs e with
          | None => None
          | Some t' =>
            match type_cast t' t with
              | None => None
              | Some cast =>
                match ED.exprD' tus tvs t' e with
                  | None => None
                  | Some x =>
                    Some (fun us gs => ED.Rcast (fun x => x) cast (x us gs))
                end
            end
        end.

    Axiom typeof_expr_exprD'
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall tus tvs e t,
        ED.typeof_expr tus tvs e = Some t ->
        exists val,
          ED.exprD' tus tvs t e = Some val.
  End with_types.
End ExprFacts.