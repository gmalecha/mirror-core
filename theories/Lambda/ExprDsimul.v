Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Option.
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

    Definition Rcast T {a b} (pf : Rty a b) : T (typD a) -> T (typD b) :=
      Relim T (Rsym pf).

    Definition Rcast_val
    : forall {a b} (pf : Rty a b), typD a -> typD b :=
      @Rcast (fun T => T).

    Definition OpenT (tus : tenv (list typ * typ)) (tvs : list typ) (T : Type) : Type :=
      hlist ctxD tus -> hlist typD tvs -> T.
    Definition Open_UseV tus tvs (n : nat)
    : option {t : typ & OpenT tus tvs (typD t)} :=
        match nth_error_get_hlist_nth typD tvs n with
          | Some (existT t get) =>
            Some
              (existT (fun t0 : typ => OpenT tus tvs (typD t0)) t
                      (fun tus => get))
          | None => None
        end.
    Definition Open_Inj tus tvs T (v : T) : OpenT tus tvs T :=
      fun _ _ => v.

    Definition Open_App {tus tvs t u}
    : OpenT tus tvs (typD (typ_arr t u)) -> OpenT tus tvs (typD t) -> OpenT tus tvs (typD u) :=
      match eq_sym (typD_arr t u) in _ = T
            return OpenT tus tvs T ->
                   OpenT tus tvs (typD t) ->
                   OpenT tus tvs (typD u)
      with
        | eq_refl => fun f x => fun us vs => (f us vs) (x us vs)
      end.

    Definition Open_Abs {tus tvs t u}
    : OpenT tus (t :: tvs) (typD u) ->
      OpenT tus tvs (typD (typ_arr t u)) :=
      match eq_sym (typD_arr t u) in _ = T
            return OpenT tus (t :: tvs) (typD u) -> OpenT tus tvs T
      with
        | eq_refl => fun f => fun us vs x => f us (Hcons x vs)
      end.

    Section OpenT.
      Definition Open_GetVAs tus tvs (n : nat) (t : typ) :
        option (OpenT tus tvs (typD t)) :=
        bind (m := option)
             (nth_error_get_hlist_nth typD tvs n)
             (fun t_get =>
                let '(existT t' get) := t_get in
                bind (m := option)
                     (type_cast t' t)
                     (fun cast =>
                        ret (fun us vs => Rcast_val cast (get vs)))).

    End OpenT.

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

    Definition func_simul (f : func) : option { t : typ & typD t } :=
      match typeof_sym f as Z
            return Z = typeof_sym f -> option _
      with
        | None => fun _ => None
        | Some T => fun pf =>
                      Some (@existT _ _ T
                                    (match pf in _ = Z
                                           return match Z with
                                                    | Some t => typD t
                                                    | None => unit
                                                  end -> typD _
                                     with
                                       | eq_refl => fun x => x
                                     end (symD f)))
      end eq_refl.

    Section exprD'.
      Variable tus : tenv (list typ * typ).

      Section uvar_eval.
        Variable exprD' : forall (tvs : tenv typ) (t : typ) (e : expr typ func),
                            option (OpenT tus tvs (typD t)).
        Context {T : Type}.
        Context {tvs : tenv typ}.

        Fixpoint uvar_eval' tys (ls : list (expr typ func)) {struct ls}
        : option ((hlist typD tys -> OpenT tus tvs T) -> OpenT tus tvs T) :=
          match tys as tys
                return option ((hlist typD tys -> OpenT tus tvs T) -> OpenT tus tvs T)
          with
            | nil => Some (fun u => u Hnil)
            | ty :: tys =>
              match ls with
                | nil => None
                | l :: ls =>
                  match exprD' tvs ty l with
                    | None => None
                    | Some val =>
                      match uvar_eval' tys ls with
                        | None => None
                        | Some result =>
                          Some (fun u => result (fun z us vs => u (Hcons (val us vs) z) us vs))
                      end
                  end
              end
          end.
      End uvar_eval.

      Fixpoint exprD' (tvs : tenv typ) (t : typ) (e : expr typ func) {struct e}
      : option (OpenT tus tvs (typD t)) :=
        match e return option (OpenT tus tvs (typD t)) with
          | Var v => @Open_GetVAs tus tvs v t
          | Inj f =>
            match @funcAs f t with
              | None => None
              | Some val =>
                Some (@Open_Inj tus tvs _ val)
            end
          | App f x =>
            match exprD'_simul tvs x with
              | None => None
              | Some (existT t' x) =>
                match exprD' tvs (typ_arr t' t) f with
                  | None => None
                  | Some f => Some (@Open_App _ _ _ _ f x)
                end
            end
          | Abs t' e =>
            arr_match (fun T => option (OpenT tus tvs T)) t
                      (fun d r =>
                         match type_cast d t' with
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
          | UVar u es =>
            bind (m := option)
             (nth_error_get_hlist_nth (fun t => hlist typD (fst t) -> typD (snd t)) tus u)
             (fun t_get =>
                let '(existT t' get) := t_get in
                bind (m := option)
                     (@uvar_eval' exprD' (typD (snd t')) tvs (fst t') es)
                     (fun val =>
                        bind (m := option)
                             (type_cast (snd t') t)
                             (fun cast =>
                                ret (fun us vs =>
                                       Rcast_val cast (val (fun z _ _ => get us z) us vs)))))
        end
      with exprD'_simul (tvs : tenv typ) (e : expr typ func) {struct e}
      : option { t : typ & OpenT tus tvs (typD t) } :=
        match e return option { t : typ & OpenT tus tvs (typD t) } with
          | Var v => @Open_UseV tus tvs v
          | Inj f =>
            match @func_simul f with
              | None => None
              | Some (existT t val) =>
                Some (@existT _ (fun t => OpenT tus tvs (typD t))
                              t (fun _ _ => val))
            end
          | App f x =>
            match exprD'_simul tvs f with
              | None => None
              | Some (existT t' f) =>
                arr_match (fun T =>
                             OpenT tus tvs T ->
                             option { t : typ & OpenT tus tvs (typD t) })
                          t'
                          (fun d r f =>
                             match exprD' tvs d x with
                               | None => None
                               | Some x =>
                                 Some (@existT _
                                               (fun t => OpenT tus tvs (typD t))
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
                Some (@existT _ (fun t => OpenT tus tvs (typD t))
                              (typ_arr t t')
                              match eq_sym (typD_arr t t') in _ = T
                                    return OpenT tus tvs T
                              with
                                | eq_refl => fun us vs x => f us (Hcons x vs)
                              end)
            end
          | UVar u es =>
            match nth_error_get_hlist_nth (fun t => hlist typD (fst t) -> typD (snd t)) tus u with
              | None => None
              | Some (existT t' get) =>
                match @uvar_eval' exprD' (typD (snd t')) tvs (fst t') es with
                  | None => None
                  | Some val =>
                    Some (@existT _ (fun t => OpenT tus tvs (typD t)) (snd t')
                                  (fun us vs => val (fun z _ _ => get us z) us vs))
                end
            end
        end.

      Definition uvar_eval
      : forall {T : Type} {tvs : tenv typ} tys
               (ls : list (expr typ func)),
          option ((hlist typD tys -> OpenT tus tvs T) -> OpenT tus tvs T) :=
        @uvar_eval' exprD'.

    End exprD'.

    Section typeof_expr.
      Variable tus : tenv (list typ * typ).

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
          | UVar x es => match nth_error tus x with
                           | None => None
                           | Some (cs,r) =>
                             (fix prefix_of cs es {struct es} : option typ :=
                                match cs with
                                  | nil => Some r
                                  | c :: cs =>
                                    match es with
                                      | nil => None
                                      | e :: es =>
                                        match typeof_expr tvs e with
                                          | None => None
                                          | Some t =>
                                            if type_cast t c then prefix_of cs es
                                            else None
                                        end
                                    end
                                end) cs es
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

    (** Equations **)
    Theorem exprD'_Var
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall tus tvs t v,
        exprD' tus tvs t (Var v) =
        bind (m := option)
             (nth_error_get_hlist_nth typD tvs v)
             (fun t_get =>
                let '(existT t' get) := t_get in
                bind (m := option)
                     (type_cast t' t)
                     (fun cast =>
                        ret (fun us vs => Rcast_val cast (get vs)))).
    Proof. reflexivity. Qed.

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
             (exprD'_simul tus tvs x)
                 (fun t_x =>
                    let '(existT t' x) := t_x in
                    bind (m := option)
                         (exprD' tus tvs (typ_arr t' t) f)
                         (fun f => ret (@Open_App _ _ _ _ f x))).
    Proof. reflexivity. Qed.

    Lemma exprD'_simul_App'
    : forall tus tvs f x,
        exprD'_simul tus tvs (App f x) =
        bind (m := option)
                      (exprD'_simul tus tvs f)
                      (fun t_f =>
                         let '(existT t' f) := t_f in
                         arr_match (fun T =>
                                      OpenT tus tvs T ->
                                      option { t : typ & OpenT tus tvs (typD t) })
                                   t'
                                   (fun d r f =>
                                      bind (m := option)
                                           (exprD' tus tvs d x)
                                           (fun x =>
                                              ret (@existT _
                                                           (fun t => OpenT tus tvs (typD t))
                                                           r
                                                           (fun us vs => (f us vs) (x us vs)))))
                                   (fun _ => None)
                                   f).
    Proof. reflexivity. Qed.

    Lemma exprD'_Abs'
    : forall tus e tvs t' t,
        exprD' tus tvs t (Abs t' e) =
        arr_match (fun T => option (OpenT tus tvs T)) t
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

    Lemma exprD'_simul_Abs'
    : forall tus e tvs t,
        exprD'_simul tus tvs (Abs t e) =
        bind (m := option)
             (exprD'_simul tus (t :: tvs) e)
             (fun t_val =>
                let '(existT t' f) := t_val in
                ret (@existT _ (fun t => OpenT tus tvs (typD t))
                             (typ_arr t t')
                             match eq_sym (typD_arr t t') in _ = T
                                   return OpenT tus tvs T
                             with
                               | eq_refl => fun us vs x => f us (Hcons x vs)
                             end)).
    Proof. reflexivity. Qed.

    Theorem exprD'_Abs
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall tus tvs t t' e,
        exprD' tus tvs t (Abs t' e) =
        arr_match (fun T => option (OpenT tus tvs T)) t
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

    Lemma exprD'_typeof_expr
    : forall tus e tvs t val,
        exprD' tus tvs t e = Some val \/
        exprD'_simul tus tvs e = Some (@existT _ _ t val) ->
        typeof_expr tus tvs e = Some t.
    Proof.
      induction e; simpl; intros.
      { unfold exprD', exprD'_simul, Open_GetVAs, Open_UseV in *. simpl in *.
        destruct H; forward; inv_all; subst;
        eapply nth_error_get_hlist_nth_Some in H0; destruct H0; simpl in *; auto.
        red in r. subst. auto. }
      { unfold exprD', exprD'_simul, func_simul, funcAs in *; simpl in *.
        generalize dependent (symD f).
        destruct (typeof_sym f).
        { destruct 1. forward. inv_all; subst. auto. }
        { destruct 2; congruence. } }
      { rewrite exprD'_App', exprD'_simul_App' in H; simpl in H.
        destruct H; forward; inv_all; subst.
        { specialize (IHe1 _ _ _ (or_introl H1)).
          specialize (IHe2 _ _ _ (or_intror H0)).
          Cases.rewrite_all_goal.
          unfold type_of_apply.
          unfold arr_match. rewrite typ2_match_zeta; eauto.
          rewrite type_cast_refl; eauto.
          rewrite eq_Const_eq. reflexivity. }
        { destruct (typ2_match_case x).
          { destruct H as [ ? [ ? [ ? ? ] ] ].
            rewrite H in *.
            specialize (IHe1 _ _ _ (or_intror H0)).
            red in x2. subst. simpl in *.
            repeat rewrite eq_Arr_eq in *.
            repeat rewrite eq_Const_eq in *.
            forward. inv_all; subst.
            specialize (IHe2 _ _ _ (or_introl H1)).
            rewrite IHe2. subst.
            unfold type_of_apply. rewrite H.
            rewrite type_cast_refl; eauto. simpl.
            rewrite eq_Const_eq. reflexivity. }
          { rewrite H in *. congruence. } } }
      { rewrite exprD'_simul_Abs', exprD'_Abs in H; eauto; destruct H.
        { destruct (typ2_match_case t0).
          { destruct H0 as [ ? [ ? [ ? ? ] ] ].
            rewrite H0 in *.
            red in x1. subst. simpl in *.
            consider (exprD' tus (t :: tvs) x0 e); intros.
            { specialize (IHe _ _ _ (or_introl H)).
              rewrite IHe.
              consider (type_cast x t); intros.
              { red in r. subst; auto. }
              { exfalso. clear - H2.
                destruct (eq_sym (typ2_cast x x0)).
                congruence. } }
            { exfalso. clear - H1. destruct (eq_sym (typ2_cast x x0)).
              destruct (type_cast x t); congruence. } }
          { rewrite H0 in H. congruence. } }
        { simpl in *. forward.
          specialize (IHe _ _ _ (or_intror H0)).
          rewrite IHe. inv_all; subst. auto. } }
      { (* unfold exprD'_simul, exprD', Open_GetUAs, Open_UseU in *. simpl in *.
        destruct H; forward; inv_all; subst;
        eapply nth_error_get_hlist_nth_Some in H0; destruct H0; auto.
        red in r. subst. auto. *)
        admit. }
    Qed.

    Lemma exprD'_deterministic
    : forall tus e tvs t1 t2 val val',
        exprD' tus tvs t1 e = Some val ->
        exprD' tus tvs t2 e = Some val' ->
        Rty t1 t2.
    Proof.
      induction e; simpl; intros; red.
      { unfold exprD', Open_GetVAs in *. simpl in *.
        forward; inv_all; subst. }
      { unfold exprD' in *; simpl in *. forward; inv_all; subst.
        unfold funcAs in *.
        generalize dependent (symD f).
        destruct (typeof_sym f); intros; try congruence.
        forward. }
      { rewrite exprD'_App' in *. simpl in *.
        forward. inv_all; subst.
        specialize (IHe1 _ _ _ _ _ H2 H1).
        eapply typ2_inj in IHe1; eauto. destruct IHe1.
        destruct H3. reflexivity. }
      { rewrite exprD'_Abs in *; eauto.
        destruct (typ2_match_case t1).
        { destruct (typ2_match_case t2).
          { forward_reason. unfold Rty in *.
            rewrite H2 in *. subst. simpl in *.
            rewrite H1 in *. clear H2 H1.
            repeat match goal with
                     | H : match ?X with eq_refl => None end = Some _ |- _ =>
                       exfalso; clear - H; destruct X; congruence
                     | H : context [ match ?X with _ => _ end ] |- _ =>
                       consider X; intros
                   end; subst.
            specialize (IHe _ _ _ _ _ H1 H3).
            red in r; red in r0.
            subst. reflexivity. }
          { rewrite H2 in *; congruence. } }
        { rewrite H1 in *. congruence. } }
      { (* unfold exprD', Open_GetUAs in *. simpl in *.
        forward; inv_all; subst. *)
        admit. }
    Qed.

    (** NOTE: These are requiring decidable equality **)
    Local Instance RelDec_eq_typ : RelDec (@eq typ) := RelDec_Rty _.
    Local Instance RelDecCorrect_eq_typ : RelDec_Correct RelDec_eq_typ :=
      _.

    Lemma exprD_simul'
    : forall tus e tvs tv,
        exprD'_simul tus tvs e = Some tv <->
        (typeof_expr tus tvs e = Some (projT1 tv) /\
         exprD' tus tvs (projT1 tv) e = Some (projT2 tv)).
    Proof.
      induction e; simpl.
      { unfold exprD'_simul, exprD', Open_UseV, Open_GetVAs. simpl. intros.
        forward; inv_all; subst; simpl.
        eapply nth_error_get_hlist_nth_Some in H0. simpl in *.
        destruct H0.
        rewrite x0. destruct tv. simpl in *.
        split; intros.
        { inv_all. subst. rewrite type_cast_refl; eauto. subst; auto. }
        { destruct H0. inv_all; subst.
          rewrite type_cast_refl in H1; eauto. inv_all; subst.
          eauto. } }
      { unfold exprD', exprD'_simul,func_simul, funcAs. simpl in *; intros.
        generalize (symD f).
        destruct (typeof_sym f).
        { split; intros; forward; inv_all; subst; simpl.
          { rewrite type_cast_refl; eauto. }
          { red in r. subst. destruct H0. destruct tv.
            simpl in *; forward; inv_all; subst.
            reflexivity. } }
        { intuition congruence. } }
      { intros. specialize (@IHe1 tvs).
        specialize (IHe2 tvs).
        rewrite exprD'_App'. rewrite exprD'_simul_App'.
        simpl in *.
        split; intros.
        { forward; inv_all; subst; simpl.
          specialize (proj1 (IHe1 _) eq_refl); clear IHe1.
          intros. forward_reason.
          Cases.rewrite_all_goal. simpl in *.
          destruct (typ2_match_case x).
          { destruct H3 as [ ? [ ? [ ? ? ] ] ].
            unfold type_of_apply.
            unfold Rty in *. subst. simpl in *.
            rewrite H3 in H1.
            destruct tv; simpl in *.
            consider (exprD'_simul tus tvs e2); intros.
            { destruct s. specialize (proj1 (IHe2 _) eq_refl); clear IHe2.
              simpl in *. intros. forward_reason.
              Cases.rewrite_all_goal. simpl in *.
              consider (exprD' tus tvs x0 e2).
              { intros.
                unfold Open_App in *. clear H3.
                specialize (exprD'_deterministic _ _ _ H1 H6).
                unfold Rty. intros; subst.
                assert (x1 = x).
                { clear - H7. destruct (eq_sym (typ2_cast x2 x1)).
                  inv_all. auto. }
                subst. Cases.rewrite_all_goal.
                rewrite type_cast_refl; eauto.
                split.
                { rewrite eq_Const_eq in *. reflexivity. }
                { unfold typ_arr. rewrite H2.
                  repeat rewrite eq_Arr_eq in *.
                  repeat rewrite eq_Const_eq in *.
                  rewrite H6 in H1.
                  inv_all; subst.
                  inv_all. subst. reflexivity. } }
              { intros. exfalso. clear - H7.
                destruct (eq_sym (typ2_cast x0 x1)).
                congruence. } }
            { exfalso.
              rewrite eq_Arr_eq in *.
              rewrite eq_Const_eq in *.
              forward. inv_all. subst. subst.
              specialize (H5 (@existT _ _ x0 o1)); simpl in *.
              rewrite H1 in *.
              erewrite exprD'_typeof_expr in H5.
              2: eauto.
              destruct H5.
              assert (Some x0 = Some x0 /\ Some o1 = Some o1); auto.
              apply H6 in H7. congruence. } }
          { rewrite H3 in H1. congruence. } }
        { destruct H. forward; inv_all; subst.
          specialize (proj1 (IHe2 _) eq_refl); clear IHe2.
          intros; forward_reason; inv_all; subst; simpl in *.
          unfold type_of_apply in *.
          destruct (typ2_match_case t).
          { destruct H0 as [ ? [ ? [ ? ? ] ] ].
            rewrite H0 in H5.
            red in x2. subst; simpl in *.
            rewrite eq_Const_eq in H5. forward.
            red in r. inv_all; subst.
            destruct tv; simpl in *.
            specialize (IHe1 (@existT _ _ (typ_arr x x0) o0)).
            simpl in *. destruct IHe1. forward_reason.
            rewrite H8. rewrite H0.
            repeat (rewrite eq_Arr_eq; rewrite eq_Const_eq).
            Cases.rewrite_all_goal. f_equal. f_equal. subst.
            unfold Open_App. clear.
            unfold typD_arr.
            generalize (typ2_cast x x0). intro.
            unfold typ_arr in *.
            generalize dependent (typD (typ2 x x0)).
            intros. revert o0. clear. subst. auto. }
          { rewrite H0 in H5. congruence. } } }
      { intros. rewrite exprD'_Abs, exprD'_simul_Abs'; eauto.
        unfold typ_arr, arr_match in *.
        simpl; split; intros; forward; inv_all; subst; simpl in *.
        { eapply IHe in H0. forward_reason. simpl in *.
          Cases.rewrite_all_goal. split; auto.
          rewrite typ2_match_zeta; auto.
          rewrite type_cast_refl; eauto.
          Cases.rewrite_all_goal.
          unfold Rcast_val.
          rewrite eq_option_eq. reflexivity. }
        { forward_reason; inv_all; subst.
          destruct tv; simpl in *; subst.
          rewrite typ2_match_zeta in H1; eauto.
          rewrite type_cast_refl in *; eauto.
          specialize (IHe (t :: tvs)).
          consider (exprD' tus (t :: tvs) t0 e).
          { intros.
            rewrite eq_option_eq in H1. inv_all; subst.
            specialize (IHe (@existT _ _ t0 o0)).
            simpl in *. destruct IHe; forward_reason.
            Cases.rewrite_all_goal.
            unfold Rcast_val. reflexivity. }
          { intros. exfalso. clear - H1.
            destruct (eq_sym (typ2_cast t t0)). congruence. } } }
      { (* unfold exprD', exprD'_simul, Open_UseU, Open_GetUAs. simpl. intros.
        forward; inv_all; subst; simpl.
        eapply nth_error_get_hlist_nth_Some in H0. simpl in *.
        destruct H0.
        rewrite x0. destruct tv. simpl in *.
        split; intros.
        { inv_all. subst. rewrite type_cast_refl; eauto. subst; auto. }
        { destruct H0. inv_all; subst.
          rewrite type_cast_refl in H1; eauto. inv_all; subst.
          reflexivity. } *) admit.  }
    Qed.

    Theorem exprD'_App
    : (* RTypeOk _ -> Typ2Ok Typ2_Fun -> RSymOk RSym_func -> *)
      forall tus tvs t f x,
        exprD' tus tvs t (App f x) =
        bind (m := option)
             (typeof_expr tus tvs x)
             (fun t' =>
                bind (exprD' tus tvs (typ_arr t' t) f)
                     (fun f =>
                        bind (exprD' tus tvs t' x)
                             (fun x =>
                                ret (Open_App f x)))).
    Proof.
      simpl. intros.
      rewrite exprD'_App'. simpl.
      consider (exprD'_simul tus tvs x); intros.
      { destruct s.
        generalize (@exprD'_typeof_expr tus x tvs _ _ (or_intror H)).
        intros. rewrite H0.
        forward.
        eapply exprD_simul' in H.
        simpl in *. destruct H.
        rewrite H2. reflexivity. }
      { consider (typeof_expr tus tvs x); auto; intros.
        consider (exprD' tus tvs (typ_arr t0 t) f); auto; intros.
        consider (exprD' tus tvs t0 x); auto; intros.
        exfalso.
        assert (exprD'_simul tus tvs x = Some (@existT _ _ t0 o0)).
        rewrite exprD_simul'. split; auto.
        congruence. }
    Qed.

    Theorem exprD'_UVar
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall tus tvs t u es,
        exprD' tus tvs t (UVar u es) =
        bind (m := option)
             (nth_error_get_hlist_nth (fun t => hlist typD (fst t) -> typD (snd t)) tus u)
             (fun t_get =>
                let '(existT t' get) := t_get in
                bind (m := option)
                     (@uvar_eval _ (typD (snd t')) tvs (fst t') es)
                     (fun val =>
                        bind (m := option)
                             (type_cast (snd t') t)
                             (fun cast =>
                                ret (fun us vs =>
                                       Rcast_val cast (val (fun z _ _ => get us z) us vs))))).
    Proof. Admitted.

    Theorem exprD'_respects
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall tus tvs t t' e (pf : Rty t' t),
        exprD' tus tvs t e =
        Rcast (fun T => option (OpenT tus tvs T)) pf
              (exprD' tus tvs t' e).
    Proof.
      destruct pf. change (eq_refl t') with (Rrefl t').
      unfold Rcast. rewrite Relim_refl; eauto with typeclass_instances.
    Qed.

  End with_types.

End ExprDenote.
