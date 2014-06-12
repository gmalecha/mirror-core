Require Import Coq.Bool.Bool.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Relations.TransitiveClosure.
Require Import ExtLib.Recur.Relation.
Require Import ExtLib.Tactics.Consider.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.ResType.
Require Import MirrorCore.LambdaM.ExprCore.

Module Type Params.
  Parameter typ : Type.
  Parameter func : Type.
End Params.

Module Make (P : Params) <: Expr with Definition typ := P.typ
                                 with Definition func := P.func.
  Definition typ := P.typ.
  Definition func := P.func.
  Definition var := nat.
  Definition uvar := nat.

  Inductive expr : Type :=
  | Var : var -> expr
  | Inj : func -> expr
  | App : expr -> expr -> expr
  | Abs : typ -> expr -> expr
  | UVar : uvar -> expr.

  Inductive expr_acc : expr -> expr -> Prop :=
  | acc_App_l : forall f a, expr_acc f (App f a)
  | acc_App_r : forall f a, expr_acc a (App f a)
  | acc_Abs : forall t e, expr_acc e (Abs t e).

  Theorem wf_expr_acc : well_founded expr_acc.
  Proof.
    clear. red.
    induction a; simpl; intros; constructor; intros;
    try solve [ inversion H ].
    { inversion H; clear H; subst; auto. }
    { inversion H; clear H; subst; auto. }
  Qed.

  Theorem expr_strong_ind
  : forall (P : expr -> Prop),
      (forall v, P (Var v)) ->
      (forall u, P (UVar u)) ->
      (forall i, P (Inj i)) ->
      (forall a b, (forall e, (leftTrans expr_acc) e (App a b) -> P e) -> P (App a b)) ->
      (forall t a, (forall e, (leftTrans expr_acc) e (Abs t a) -> P e) -> P (Abs t a)) ->
      forall e, P e.
  Proof.
    intros P Hvar Huvar Hinj Happ Habs.
    eapply Fix. eapply wf_leftTrans. eapply wf_expr_acc.
    destruct x; auto.
  Qed.

  Section eq_dec.

    Variable RelDec_eq_typ : RelDec (@eq typ).
    Variable RelDec_eq_func : RelDec (@eq func).

    Fixpoint expr_eq_dec (e1 e2 : expr) : bool :=
      match e1 , e2 with
        | Var v1 , Var v2 => EqNat.beq_nat v1 v2
        | UVar v1 , UVar v2 => EqNat.beq_nat v1 v2
        | Inj f1 , Inj f2 =>
          f1 ?[ eq ] f2
        | App f1 e1 , App f2 e2 =>
          if expr_eq_dec f1 f2 then
            expr_eq_dec e1 e2
          else
            false
        | Abs t1 e1 , Abs t2 e2 =>
          if t1 ?[ eq ] t2 then expr_eq_dec e1 e2
          else false
        | _ , _ => false
      end.

    Variable RelDec_Correct_typ : RelDec_Correct RelDec_eq_typ.
    Variable RelDec_Correct_func : RelDec_Correct RelDec_eq_func.

    Theorem expr_eq_dec_eq : forall e1 e2,
                               expr_eq_dec e1 e2 = true <-> e1 = e2.
    Proof.
      induction e1; destruct e2; simpl; intros;
      repeat match goal with
               | |- context [ if ?X then ?Y else false ] =>
                 change (if X then Y else false) with (andb X Y)
               | |- context [ EqNat.beq_nat ?X ?Y ] =>
                 change (EqNat.beq_nat X Y) with (X ?[ eq ] Y) ;
                   rewrite rel_dec_correct
               | |- context [ ?X ?[ ?Z ] ?Y ] =>
                 rewrite rel_dec_correct
               | |- context [ ?X ?[ @eq ?T ]?Y ] =>
                 change (X ?[ @eq T ] Y) with (X ?[ eq ] Y) ;
                   rewrite rel_dec_correct
               | |- context [ List.list_eqb RelDec_eq_typ ?X ?Y ] =>
                 change (List.list_eqb RelDec_eq_typ X Y) with (X ?[ eq ] Y) ;
                   rewrite rel_dec_correct
               | |- _ => rewrite andb_true_iff
               | H : forall x, (_ = true) <-> _ |- _ => rewrite H
             end; try solve [ intuition congruence ].
    Qed.

    Global Instance RelDec_eq_expr : RelDec (@eq expr) :=
      { rel_dec := expr_eq_dec }.

    Global Instance RelDecCorrect_eq_expr : RelDec_Correct RelDec_eq_expr.
    Proof.
      constructor. eapply expr_eq_dec_eq.
    Qed.
  End eq_dec.

  Section denotation.
    Context {RType_typD : RType typ}.
    Context {Typ2_Fun : Typ2 RType_typD Fun}.
    Context {RSym_func : RSym func}.

    (** Reasoning principles **)
    Context {RTypeOk_typD : @RTypeOk _ _}.
    Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.
    Context {RSymOk_func : RSymOk RSym_func}.

    Let typ_arr : typ -> typ -> typ := @typ2 _ _ _ _.
    Let arr_match := @typ2_match _ _ _ _.
    Let typD_arr
    : forall ts a b, typD ts (typ_arr a b) = (typD ts a -> typD ts b)
      := @typ2_cast _ _ _ _.

    Definition Rcast T {ts a b} (pf : Rty ts a b)
    : T (typD ts a) -> T (typD ts b) :=
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

    Section exprD'.
      Variable ts : list Type.
      Variable tus : tenv typ.

      Fixpoint exprD' (tvs : tenv typ) (t : typ) (e : expr)
      : option (OpenT ts tus tvs (typD ts t)) :=
        match e return option (OpenT ts tus tvs (typD ts t)) with
          | Var v =>
            match nth_error_get_hlist_nth (typD ts) tvs v with
              | Some (existT t' get) =>
                match type_cast ts t t' with
                  | Some cast =>
                    Some (Relim (OpenT ts tus tvs) cast (fun us vs => get vs))
                  | None => None
                end
              | None => None
            end
          | Inj f =>
            match typeof_sym f as Z
                  return Z = typeof_sym f ->
                         option (OpenT ts tus tvs (typD ts t))
            with
              | None => fun _ => None
              | Some T => fun pf =>
                            match type_cast ts t T with
                              | None => None
                              | Some cast =>
                                Some (Relim (OpenT ts tus tvs) cast
                                            (match pf in _ = Z
                                                   return match Z with
                                                            | Some t => typD nil t
                                                            | None => unit
                                                          end -> OpenT ts tus tvs (typD ts _)
                                             with
                                               | eq_refl => fun x =>
                                                              (@Open_Inj _ _ _ _ (type_weaken ts _ x))
                                             end (symD f)))
                            end
            end eq_refl
          | App f x =>
            match exprD'_simul tvs x with
              | None => None
              | Some (existT t' x) =>
                match exprD' tvs (typ_arr t' t) f with
                  | None => None
                  | Some f => Some (@Open_App ts _ _ _ _ f x)
                end
            end
          | Abs t' e =>
            arr_match (fun T => option (OpenT ts tus tvs T)) ts t
                      (fun d r =>
                         match type_cast ts d t' with
                           | None => None
                           | Some cast =>
                             match exprD' (t' :: tvs) r e with
                               | None => None
                               | Some val =>
                                 Some (fun us vs x =>
                                         val us (Hcons (Rcast_val cast x) vs))
                             end
                         end)
                      None
          | UVar u =>
            match nth_error_get_hlist_nth (typD ts) tus u with
              | Some (existT t' get) =>
                match type_cast ts t t' with
                  | Some cast =>
                    Some (Relim (OpenT ts tus tvs) cast (fun us vs => get us))
                  | None => None
                end
              | None => None
            end
        end

      with exprD'_simul (tvs : tenv typ) (e : expr)
      : option { t : typ & OpenT ts tus tvs (typD ts t) } :=
        match e return option { t : typ & OpenT ts tus tvs (typD ts t) } with
          | Var v => @Open_UseV _ (typD ts) tus tvs v
          | Inj f =>
            match typeof_sym f as Z
                  return Z = typeof_sym f -> option _
            with
              | None => fun _ => None
              | Some T => fun pf =>
                Some (@existT _ _ T
                              (match pf in _ = Z
                                     return match Z with
                                              | Some t => typD nil t
                                              | None => unit
                                            end -> OpenT ts tus tvs (typD ts _)
                               with
                                 | eq_refl => fun x =>
                                   Open_Inj ts tus tvs _ (type_weaken ts _ x)
                               end (symD f)))
            end eq_refl
          | App f x =>
            match exprD'_simul tvs f with
              | None => None
              | Some (existT t' f) =>
                arr_match (fun T =>
                             OpenT ts tus tvs T ->
                             option { t : typ & OpenT ts tus tvs (typD ts t) })
                          ts t'
                          (fun d r f =>
                             match exprD' tvs d x with
                               | None => None
                               | Some x =>
                                 Some (@existT _
                                               (fun t => OpenT ts tus tvs (typD ts t))
                                               r
                                               (fun us vs => (f us vs) (x us vs)))
                             end)
                          (fun _ => None)
                          f
            end
          | Abs t e =>
            match exprD'_simul (t :: tvs) e with
              | None => None
              | Some (existT t' f) =>
                Some (@existT _ (fun t => OpenT ts tus tvs (typD ts t))
                              (typ_arr t t')
                              match eq_sym (typD_arr ts t t') in _ = T
                                    return OpenT ts tus tvs T
                              with
                                | eq_refl => fun us vs x => f us (Hcons x vs)
                              end)
            end
          | UVar u => Open_UseU _ _ tus tvs u
        end.
    End exprD'.

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

      Fixpoint typeof_expr (tvs : tenv typ) (e : expr)
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

    Theorem exprD'_respects
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall ts tus tvs t t' e (pf : Rty ts t' t),
        exprD' ts tus tvs t e =
        Rcast (fun T => option (OpenT ts tus tvs T)) pf (exprD' ts tus tvs t' e).
    Proof. clear. destruct pf. reflexivity. Qed.

    Theorem exprD'_Var
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
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
    Proof. clear. Admitted.

    Theorem exprD'_UVar
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
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
    Proof. clear. Admitted.

    Theorem exprD'_Inj
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall ts tus tvs t s,
        exprD' ts tus tvs t (Inj s) =
        bind (m := option)
             (funcAs s t)
             (fun val =>
                ret (fun _ _ => val)).
    Proof. clear. Admitted.

    Theorem exprD'_App
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
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
    Proof. clear. Admitted.

    Theorem exprD'_Abs
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
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
    Proof. clear. Admitted.

  End denotation.
End Make.