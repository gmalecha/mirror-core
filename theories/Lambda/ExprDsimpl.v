Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprDI.

Set Implicit Arguments.
Set Strict Implicit.

Module ExprDenote <: ExprDenote.

  Section with_types.
    Context {typ : Type}.
    Context {func : Type}.
    Context {RType_typD : RType typ}.
    Context {Typ2_Fun : Typ2 _ Fun}.
    Context {RSym_func : RSym func}.

    (** Reasoning principles **)
    Context {RTypeOk_typD : RTypeOk}.
    Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.
    Context {RSymOk_func : RSymOk RSym_func}.

    Let typ_arr : typ -> typ -> typ := @typ2 _ _ _ _.
    Let arr_match := @typ2_match _ _ _ _.
    Let typD_arr
    : forall a b, typD (typ_arr a b) = (typD a -> typD b)
      := @typ2_cast _ _ _ _.


    Global Instance RelDec_Rty : RelDec Rty :=
    { rel_dec := fun a b => match type_cast a b with
                              | Some _ => true
                              | None => false
                            end }.

    Global Instance RelDec_Correct_Rty : @RelDec_Correct _ Rty _.
    Proof.
      constructor. unfold rel_dec; simpl.
      intros; consider (type_cast x y); intros.
      split; auto. apply type_cast_total in H; eauto with typeclass_instances.
      intuition.
    Qed.

    Definition Rcast T {a b} (pf : Rty a b) : T (typD a) -> T (typD b) :=
      Relim T (Rsym pf).

    Definition Rcast_val
    : forall {a b} (pf : Rty a b), typD a -> typD b :=
      @Rcast (fun T => T).

(*
    Definition OpenT ts := ResType.OpenT (typD ts).
    Definition Open_UseV := ResType.Open_UseV.
    Definition Open_UseU := ResType.Open_UseU.
*)
    Instance Applicative_exprT tus tvs : Applicative (exprT tus tvs) :=
    { pure := fun _ x _ _ => x
    ; ap   := fun _ _ f g x y => (f x y) (g x y)
    }.

    Definition exprT_Inj tus tvs : forall T, T -> exprT tus tvs T :=
      Eval simpl in @pure (@exprT typ RType_typD tus tvs) _.

    Definition exprT_App {tus tvs t u}
    : exprT tus tvs (typD (typ_arr t u)) -> exprT tus tvs (typD t) -> exprT tus tvs (typD u) :=
      match eq_sym (typD_arr t u) in _ = T
            return exprT tus tvs T ->
                   exprT tus tvs (typD t) ->
                   exprT tus tvs (typD u)
      with
        | eq_refl => fun f x => fun us vs => (f us vs) (x us vs)
      end.

    Section OpenT.
      Variable tus : tenv (ctyp typ).
      Variable tvs : tenv typ.

      (** Auxiliary definitions **)
(*
      Definition Open_GetUAs (n : nat) (t : typ) :
        option (exprT tus tvs (typD t)) :=
        bind (m := option)
             (nth_error_get_hlist_nth ctxD tus n)
             (fun t_get =>
                let '(existT t' get) := t_get in
                bind (m := option)
                     (type_cast t' t)
                     (fun cast =>
                        ret (fun us vs => Rcast_val cast (get us)))).
*)

      Definition Open_GetVAs (n : nat) (t : typ) :
        option (exprT tus tvs (typD t)) :=
        bind (m := option)
             (nth_error_get_hlist_nth (typD) tvs n)
             (fun t_get =>
                let '(existT t' get) := t_get in
                bind (m := option)
                     (type_cast t' t)
                     (fun cast =>
                        ret (fun us vs => Rcast_val cast (get vs)))).

    End OpenT.

    Definition Open_Abs {tus tvs t u}
    : exprT tus (t :: tvs) (typD u) ->
      exprT tus tvs (typD (typ_arr t u)) :=
      match eq_sym (typD_arr t u) in _ = T
            return exprT tus (t :: tvs) (typD u) -> exprT tus tvs T
      with
        | eq_refl => fun f => fun us vs x => f us (Hcons x vs)
      end.

    Definition funcAs (f : func) (t : typ) : option (typD t) :=
      match typeof_sym f as Z
            return Z = typeof_sym f -> option (typD t)
      with
        | None => fun _ => None
        | Some T => fun pf =>
                      match type_cast T t with
                        | None => None
                        | Some cast =>
                          Rcast option cast
                                (Some (match pf in _ = Z
                                             return match Z with
                                                      | Some t => typD t
                                                      | None => unit
                                                    end -> typD _
                                       with
                                         | eq_refl => fun x => x
                                       end (symD f)))
                      end
      end eq_refl.

    Section typeof_expr.
      Variable tus : tenv (ctyp typ).

      Definition type_of_apply (tv x : typ) : option typ :=
        arr_match (fun _ => option typ) tv
                  (fun d r =>
                     match type_cast d x with
                       | Some _ => Some r
                       | None => None
                     end)
                  None.

      Require Import ExtLib.Structures.Traversable.
      Require Import ExtLib.Data.List.

      Fixpoint typeof_expr (tvs : tenv typ) (e : expr typ func) {struct e}
      : option typ :=
        match e with
        | Var x  => nth_error tvs x
        | UVar x es =>
          match nth_error tus x with
            | None => None
            | Some {| cctx := ctx ; vtyp := vtyp |} =>
              match mapT_list _ _ (typeof_expr tvs) es with
                | None => None
                | Some ts =>
                  if ts ?[ eq ] ctx then Some vtyp else None
              end
          end
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
      Variable tus : tenv (ctyp typ).

      Fixpoint applyEach tvs (rec : forall t, expr typ func -> option (exprT tus tvs (typD t)))
               (ls : list typ) (es : list (expr typ func)) rT {struct es}
      : option (ctxD {| cctx := ls ; vtyp := rT |} -> exprT tus tvs (typD rT)) :=
        match ls as ls , es
              return option (ctxD {| cctx := ls ; vtyp := rT |} -> exprT tus tvs (typD rT))
        with
          | nil , nil => Some (fun x _ _ => x Hnil)
          | nil , _ :: _ => None
          | _ :: _ , nil => None
          | l :: ls , e :: es =>
            match rec l e
                , applyEach rec ls es rT
            with
              | None , _ => None
              | Some _ , None => None
              | Some eD , Some rD => Some (fun f us vs => rD (fun x => f (Hcons (eD us vs) x)) us vs)
            end
        end.

      Fixpoint exprD' (tvs : tenv typ) (t : typ) (e : expr typ func)
      : option (exprT tus tvs (typD t)) :=
        match e return option (exprT tus tvs (typD t)) with
          | Var v => @Open_GetVAs tus tvs v t
          | Inj f =>
            bind (m := option)
                 (@funcAs f t)
                 (fun val =>
                    ret (@exprT_Inj tus tvs _ val))
          | App f x =>
            bind (m := option)
                 (typeof_expr tus tvs x)
                 (fun d =>
                    bind (m := option)
                         (exprD' tvs (typ_arr d t) f)
                         (fun f =>
                            bind (m := option)
                                 (exprD' tvs d x)
                                 (fun x => ret (@exprT_App _ _ _ _ f x))))
          | Abs t' e =>
            arr_match (fun T => option (exprT tus tvs T)) t
                      (fun d r =>
                         bind (m := option)
                              (type_cast d t')
                              (fun cast =>
                                 bind (m := option)
                                      (exprD' (t' :: tvs) r e)
                                      (fun val =>
                                         ret (fun us vs x =>
                                                val us (Hcons (Rcast_val cast x) vs)))))
                      None
          | UVar u es => (* @Open_GetUAs ts tus tvs u t *)
            bind (m := option)
                 (OpenT.OpenT_Use ctxD tus  u)
                 (fun ctx_val =>
                    None

)
        end.
    End exprD'.

    (** Equations **)
    Theorem exprD'_Var
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall tus tvs t v,
        exprD' tus tvs t (Var v) =
        bind (m := option)
             (nth_error_get_hlist_nth (typD) tvs v)
             (fun t_get =>
                let '(existT t' get) := t_get in
                bind (m := option)
                     (type_cast t' t)
                     (fun cast =>
                        ret (fun us vs => Rcast_val cast (get vs)))).
    Proof. reflexivity. Qed.

(*
    Theorem exprD'_UVar
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall tus tvs t u es,
        exprD' tus tvs t (UVar u es) =
        bind (m := option)
             (nth_error_get_hlist_nth (typD) tus u)
             (fun t_get =>
                let '(existT t' get) := t_get in
                bind (m := option)
                     (type_cast t' t)
                     (fun cast =>
                        ret (fun us vs => Rcast_val cast (get us)))).
    Proof. reflexivity. Qed.
*)

    Theorem exprD'_Inj
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall tus tvs t s,
        exprD' tus tvs t (Inj s) =
        bind (m := option)
             (funcAs s t)
             (fun val =>
                ret (fun _ _ => val)).
    Proof. reflexivity. Qed.

    Lemma exprD'_App'
    : forall tus tvs t f x,
        exprD' tus tvs t (App f x) =
        bind (m := option)
             (typeof_expr tus tvs x)
             (fun d =>
                bind (m := option)
                     (exprD' tus tvs (typ_arr d t) f)
                     (fun f =>
                        bind (m := option)
                             (exprD' tus tvs d x)
                             (fun x => ret (@exprT_App _ _ _ _ f x)))).
    Proof. reflexivity. Qed.

    Theorem exprD'_Abs
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall tus tvs t t' e,
        exprD' tus tvs t (Abs t' e) =
        arr_match (fun T => option (exprT tus tvs T)) t
                  (fun d r =>
                     bind (m := option)
                          (type_cast d t')
                          (fun cast =>
                             bind (m := option)
                                  (exprD' tus (t' :: tvs) r e)
                                  (fun val =>
                                     ret (fun us vs x =>
                                            val us (Hcons (Rcast_val cast x) vs)))))
                  None.
    Proof. reflexivity. Qed.

    Theorem exprD'_App
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall tus tvs t f x,
        exprD' tus tvs t (App f x) =
        bind (m := option)
             (typeof_expr tus tvs x)
             (fun t' =>
                bind (exprD' tus tvs (typ_arr t' t) f)
                     (fun f =>
                        bind (exprD' tus tvs t' x)
                             (fun x =>
                                ret (exprT_App f x)))).
    Proof. reflexivity. Qed.

    Theorem exprD'_respects
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall tus tvs t t' e (pf : Rty t' t),
        exprD' tus tvs t e =
        Rcast (fun T => option (exprT tus tvs T)) pf
              (exprD' tus tvs t' e).
    Proof.
      destruct pf. change (eq_refl t') with (Rrefl t').
      unfold Rcast. rewrite Relim_refl; eauto with typeclass_instances.
    Qed.

  End with_types.

End ExprDenote.
