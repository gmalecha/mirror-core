Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Lambda.TypesI2.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprDI.

Set Implicit Arguments.
Set Strict Implicit.

Module ExprDenote <: ExprDenote.

  Section with_types.
    Context {func : Type}.
    Context {RType_typD : RType}.
    Context {Typ2_Fun : Typ2 _ Fun}.
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

    Section OpenT.
      Variable ts : list Type.
      Variables tus tvs : tenv typ.

      Definition OpenT (T : Type) :=
        hlist (typD ts) tus -> hlist (typD ts) tvs -> T.

      Definition Open_UseV (n : nat) : option { t : typ & OpenT (typD ts t) } :=
        bind (m := option)
             (nth_error_get_hlist_nth _ tvs n)
             (fun t_get =>
                let '(existT t get) := t_get in
                ret (@existT _ (fun t => OpenT (typD ts t)) t
                             (fun us vs => get vs))).

      Definition Open_UseU (n : nat) : option { t : typ & OpenT (typD ts t) } :=
        bind (m := option)
             (nth_error_get_hlist_nth _ tus n)
             (fun t_get =>
                let '(existT t get) := t_get in
                ret (@existT _ (fun t => OpenT (typD ts t)) t
                             (fun us vs => get us))).

      Definition Open_App {t u}
      : OpenT (typD ts (typ_arr t u)) -> OpenT (typD ts t) -> OpenT (typD ts u) :=
        match eq_sym (typD_arr ts t u) in _ = T
              return OpenT T -> OpenT (typD ts t) -> OpenT (typD ts u)
        with
          | eq_refl => fun f x => fun us vs => (f us vs) (x us vs)
        end.

      Definition Open_Inj {t} (val : typD ts t)
      : OpenT (typD ts t) :=
        fun _ _ => val.


      (** Auxiliary definitions **)
      Definition Open_GetUAs (n : nat) (t : typ) :
        option (OpenT (typD ts t)) :=
        bind (m := option)
             (nth_error_get_hlist_nth (typD ts) tus n)
             (fun t_get =>
                let '(existT t' get) := t_get in
                bind (m := option)
                     (type_cast ts t' t)
                     (fun cast =>
                        ret (fun us vs => Rcast_val cast (get us)))).

      Definition Open_GetVAs (n : nat) (t : typ) :
        option (OpenT (typD ts t)) :=
        bind (m := option)
             (nth_error_get_hlist_nth (typD ts) tvs n)
             (fun t_get =>
                let '(existT t' get) := t_get in
                bind (m := option)
                     (type_cast ts t' t)
                     (fun cast =>
                        ret (fun us vs => Rcast_val cast (get vs)))).

    End OpenT.

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

    Section exprD'.
      Variable ts : list Type.
      Variable tus : tenv typ.

      Fixpoint exprD' (tvs : tenv typ) (t : typ) (e : expr typ func)
      : option (OpenT ts tus tvs (typD ts t)) :=
        match e return option (OpenT ts tus tvs (typD ts t)) with
          | Var v => @Open_GetVAs ts tus tvs v t
          | Inj f =>
            bind (m := option)
                 (@funcAs _ f t)
                 (fun val =>
                    ret (@Open_Inj ts tus tvs t val))
          | App f x =>
            bind (m := option)
                 (typeof_expr ts tus tvs x)
                 (fun d =>
                    bind (m := option)
                         (exprD' tvs (typ_arr d t) f)
                         (fun f =>
                            bind (m := option)
                                 (exprD' tvs d x)
                                 (fun x => ret (@Open_App ts _ _ _ _ f x))))
          | Abs t' e =>
            arr_match (fun T => option (OpenT ts tus tvs T)) ts t
                      (fun d r =>
                         bind (m := option)
                              (type_cast ts d t')
                              (fun cast =>
                                 bind (m := option)
                                      (exprD' (t' :: tvs) r e)
                                      (fun val =>
                                         ret (fun us vs x =>
                                                val us (Hcons (Rcast_val cast x) vs)))))
                      None
          | UVar u => @Open_GetUAs ts tus tvs u t
        end.
    End exprD'.

    (** Equations **)
    Theorem exprD'_Var
    : RTypeOk _ -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
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
    Proof. reflexivity. Qed.

    Theorem exprD'_UVar
    : RTypeOk _ -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
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
    Proof. reflexivity. Qed.

    Theorem exprD'_Inj
    : RTypeOk _ -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall ts tus tvs t s,
        exprD' ts tus tvs t (Inj s) =
        bind (m := option)
             (funcAs s t)
             (fun val =>
                ret (fun _ _ => val)).
    Proof. reflexivity. Qed.

    Lemma exprD'_App'
    : forall ts tus tvs t f x,
        exprD' ts tus tvs t (App f x) =
        bind (m := option)
             (typeof_expr ts tus tvs x)
             (fun d =>
                bind (m := option)
                     (exprD' ts tus tvs (typ_arr d t) f)
                     (fun f =>
                        bind (m := option)
                             (exprD' ts tus tvs d x)
                             (fun x => ret (@Open_App ts _ _ _ _ f x)))).
    Proof. reflexivity. Qed.

    Theorem exprD'_Abs
    : RTypeOk _ -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
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
    Proof. reflexivity. Qed.

    Theorem exprD'_App
    : RTypeOk _ -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
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
    Proof. reflexivity. Qed.

    Theorem exprD'_respects
    : RTypeOk _ -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall ts tus tvs t t' e (pf : Rty ts t' t),
        exprD' ts tus tvs t e =
        Rcast (fun T => option (OpenT ts tus tvs T)) pf
              (exprD' ts tus tvs t' e).
    Proof.
      destruct pf. change (eq_refl t') with (Rrefl ts t').
      unfold Rcast. rewrite Relim_refl; eauto with typeclass_instances.
    Qed.

  End with_types.

End ExprDenote.
