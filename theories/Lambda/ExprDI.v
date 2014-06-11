Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Lambda.TypesI2.
Require Import MirrorCore.Lambda.ResType.
Require Import MirrorCore.Lambda.ExprCore.

Set Implicit Arguments.
Set Strict Implicit.

Module Type ExprDenote.

  Section with_types.
    Context {func : Type}.
    Context {RType_typD : RType}.
    Context {Typ2_Fun : Typ2 RType_typD Fun}.
    Context {RSym_func : RSym typD func}.

    (** Reasoning principles **)
    Context {RTypeOk_typD : @RTypeOk _}.
    Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.
    Context {RSymOk_func : RSymOk RSym_func}.

    Let typ_arr : typ -> typ -> typ := @typ2 _ _ _.
    Let arr_match := @typ2_match _ _ _.
    Let typD_arr
    : forall ts a b, typD ts (typ_arr a b) = (typD ts a -> typD ts b)
      := @typ2_cast _ _ _.


    Global Instance RelDec_Rty ts : RelDec (Rty ts) :=
    { rel_dec := fun a b => match type_cast ts a b with
                              | Some _ => true
                              | None => false
                            end }.

    Global Instance RelDec_Correct_Rty ts : @RelDec_Correct _ (Rty ts) _.
    Proof.
      constructor. unfold rel_dec; simpl.
      intros; consider (type_cast ts x y); intros.
      split; auto. apply type_cast_total in H; eauto with typeclass_instances.
      intuition.
    Qed.

    Definition Rcast T {ts a b} (pf : Rty ts a b) : T (typD ts a) -> T (typD ts b) :=
      Relim T (Rsym pf).

    Definition Rcast_val
    : forall {ts a b} (pf : Rty ts a b), typD ts a -> typD ts b :=
      @Rcast (fun T => T).

    Definition OpenT ts := ResType.OpenT (typD ts).
    Definition Open_UseV := ResType.Open_UseV.
    Definition Open_UseU := ResType.Open_UseU.
    Definition Open_Inj ts tus tvs := Eval simpl in @pure (OpenT ts tus tvs) _.

    Definition Open_App {ts tus tvs t u}
    : OpenT ts tus tvs (typD ts (typ_arr t u)) -> OpenT ts tus tvs (typD ts t) -> OpenT ts tus tvs (typD ts u) :=
      match eq_sym (typD_arr ts t u) in _ = T
            return OpenT ts tus tvs T ->
                   OpenT ts tus tvs (typD ts t) ->
                   OpenT ts tus tvs (typD ts u)
      with
        | eq_refl => fun f x => fun us vs => (f us vs) (x us vs)
      end.

    Definition Open_Abs {ts tus tvs t u}
    : OpenT ts tus (t :: tvs) (typD ts u) ->
      OpenT ts tus tvs (typD ts (typ_arr t u)) :=
      match eq_sym (typD_arr ts t u) in _ = T
            return OpenT ts tus (t :: tvs) (typD ts u) -> OpenT ts tus tvs T
      with
        | eq_refl => fun f => fun us vs x => f us (Hcons x vs)
      end.

    Definition funcAs {ts} (f : func) (t : typ) : option (typD ts t) :=
      match typeof_sym f as Z
            return Z = typeof_sym f -> option (typD ts t)
      with
        | None => fun _ => None
        | Some T => fun pf =>
                      match type_cast ts T t with
                        | None => None
                        | Some cast =>
                          Rcast option cast
                                (Some (match pf in _ = Z
                                             return match Z with
                                                      | Some t => typD nil t
                                                      | None => unit
                                                    end -> typD ts _
                                       with
                                         | eq_refl => fun x => type_weaken ts _ x
                                       end (symD f)))
                      end
      end eq_refl.

    Parameter exprD'
    : forall {Typ2_Fun : Typ2 _ Fun}
             {RSym_func : RSym typD func}
             ts (tus tvs : tenv typ) (t : typ) (e : expr typ func),
        option (OpenT ts tus tvs (typD ts t)).

    Axiom exprD'_respects
    : @RTypeOk _ -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall ts tus tvs t t' e (pf : Rty ts t' t),
        exprD' ts tus tvs t e =
        Rcast (fun T => option (OpenT ts tus tvs T)) pf (exprD' ts tus tvs t' e).

    Section typeof_expr.
      Variable ts : list Type.
      Variable tus : tenv typ.

      Definition type_of_apply (tv x : typ) : option typ :=
        arr_match (fun _ => option typ) ts tv
                  (fun d r =>
                     match type_cast ts d x with
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
    : @RTypeOk _ -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall ts tus tvs t v,
        exprD' ts tus tvs t (Var v) =
        bind (m := option)
             (nth_error_get_hlist_nth (typD ts) tvs v)
             (fun t_get =>
                let '(existT t' get) := t_get in
                bind (m := option)
                     (type_cast ts t' t)
                     (fun cast =>
                        ret (fun us vs => Rcast_val cast (get vs)))).

    Axiom exprD'_UVar
    : @RTypeOk _ -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall ts tus tvs t u,
        exprD' ts tus tvs t (UVar u) =
        bind (m := option)
             (nth_error_get_hlist_nth (typD ts) tus u)
             (fun t_get =>
                let '(existT t' get) := t_get in
                bind (m := option)
                     (type_cast ts t' t)
                     (fun cast =>
                        ret (fun us vs => Rcast_val cast (get us)))).

    Axiom exprD'_Inj
    : @RTypeOk _ -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall ts tus tvs t s,
        exprD' ts tus tvs t (Inj s) =
        bind (m := option)
             (funcAs s t)
             (fun val =>
                ret (fun _ _ => val)).

    Axiom exprD'_App
    : @RTypeOk _ -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall ts tus tvs t f x,
        exprD' ts tus tvs t (App f x) =
        bind (m := option)
             (typeof_expr ts tus tvs x)
             (fun t' =>
                bind (exprD' ts tus tvs (typ_arr t' t) f)
                     (fun f =>
                        bind (exprD' ts tus tvs t' x)
                             (fun x =>
                                ret (Open_App f x)))).

    Axiom exprD'_Abs
    : @RTypeOk _ -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall ts tus tvs t t' e,
        exprD' ts tus tvs t (Abs t' e) =
        arr_match (fun T => option (OpenT ts tus tvs T)) ts t
                  (fun d r =>
                     bind (m := option)
                          (type_cast ts d t')
                          (fun cast =>
                             bind (m := option)
                                  (exprD' ts tus (t' :: tvs) r e)
                                  (fun val =>
                                     ret (fun us vs x =>
                                            val us (Hcons (Rcast_val cast x) vs)))))
                  None.

  End with_types.

End ExprDenote.

Module Type ExprFacts (ED : ExprDenote).

  Section with_types.
    Context {RType_typD : RType}.
    Context {Typ2_Fun : Typ2 _ Fun}.
    Context {func : Type}.
    Context {RSym_func : RSym typD func}.

    (** Reasoning principles **)
    Context {RTypeOk_typD : @RTypeOk _}.
    Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.
    Context {RSymOk_func : RSymOk RSym_func}.

    Axiom exprD'_ind
    : @RTypeOk _ -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall (P : forall ts tus tvs, _ -> forall t, option (ED.OpenT _ tus tvs (typD ts t)) -> Prop) ts tus
        (Hnone : forall ts tus tvs e t,
                   ED.exprD' ts tus tvs t e = None -> P ts tus tvs e t None)
        (Hvar : forall tvs v t t' get (pf : Rty ts t t'),
                  nth_error_get_hlist_nth _ tvs v = Some (@existT _ _ t' get) ->
                  P ts tus tvs (Var v) t
                    (Some (Relim (ED.OpenT ts tus tvs) pf (fun _ (vs : hlist _ tvs) => get vs))))
        (Huvar : forall tvs u t t' get (pf : Rty ts t t'),
                   nth_error_get_hlist_nth _ tus u = Some (@existT _ _ t' get) ->
                   P ts tus tvs (UVar u) t
                     (Some (Relim (ED.OpenT ts tus tvs) pf ((fun us _ => get us)))))
        (Hinj : forall tvs i t t' (pf : typeof_sym i = Some t)
                (pf' : Rty ts t' t),
                  P ts tus tvs (Inj i) t'
                    (Some (Relim (ED.OpenT ts tus tvs) pf' (fun _ _ =>
                             type_weaken ts _ match pf in _ = t
                                                    return match t with
                                                             | Some t => typD nil t
                                                             | None => unit
                                                           end with
                                                | eq_refl => symD i
                                              end))))
        (Happ : forall tvs d r f x fval xval,
                  ED.typeof_expr ts tus tvs x = Some d ->
                  P ts tus tvs f (typ2 d r) (Some fval) ->
                  P ts tus tvs x d (Some xval) ->
                  P ts tus tvs (App f x) r
                    (Some (ED.Open_App fval xval)))
        (Habs : forall tvs d r e fval,
                  P ts tus (d :: tvs) e r (Some fval) ->
                  P ts tus tvs (Abs d e) (typ2 d r) (Some (ED.Open_Abs fval))),
        forall tvs e t,
        P ts tus tvs e t (ED.exprD' ts tus tvs t e).

    Axiom typeof_expr_weaken
    : @RTypeOk _ -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall ts tus tvs e t tus' tvs',
        ED.typeof_expr ts tus tvs e = Some t ->
        ED.typeof_expr ts (tus ++ tus') (tvs ++ tvs') e = Some t.

    Axiom exprD'_weaken
    : @RTypeOk _ -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall ts tus tvs (e : expr typ func) t val tus' tvs',
        ED.exprD' ts tus tvs t e = Some val ->
        exists val',
          ED.exprD' ts (tus ++ tus') (tvs ++ tvs') t e = Some val' /\
          forall us vs us' vs',
            val us vs = val' (hlist_app us us') (hlist_app vs vs').

    Axiom exprD'_type_cast
    : @RTypeOk _ -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall ts tus tvs e t,
        ED.exprD' ts tus tvs t e =
        match ED.typeof_expr ts tus tvs e with
          | None => None
          | Some t' =>
            match @type_cast _ ts t' t with
              | None => None
              | Some cast =>
                match ED.exprD' ts tus tvs t' e with
                  | None => None
                  | Some x =>
                    Some (fun us gs => ED.Rcast (fun x => x) cast (x us gs))
                end
            end
        end.

    Axiom typeof_expr_exprD'
    : @RTypeOk _ -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall ts tus tvs e t,
        ED.typeof_expr ts tus tvs e = Some t ->
        exists val,
          ED.exprD' ts tus tvs t e = Some val.
  End with_types.
End ExprFacts.
