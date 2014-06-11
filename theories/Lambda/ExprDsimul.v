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

    Definition OpenT ts :=
      ResType.OpenT (typD ts).
    Definition Open_UseV :=
      Eval red in ResType.Open_UseV.
    Definition Open_UseU :=
      Eval red in ResType.Open_UseU.
    Definition Open_Inj ts tus tvs :=
      Eval simpl in @pure (OpenT ts tus tvs) _.

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

    Section OpenT.
      Variable ts : list Type.
      Variables tus tvs : tenv typ.

      (** Auxiliary definitions **)
      Definition Open_GetUAs (n : nat) (t : typ) :
        option (OpenT ts tus tvs (typD ts t)) :=
        bind (m := option)
             (nth_error_get_hlist_nth (typD ts) tus n)
             (fun t_get =>
                let '(existT t' get) := t_get in
                bind (m := option)
                     (type_cast ts t' t)
                     (fun cast =>
                        ret (fun us vs => Rcast_val cast (get us)))).

      Definition Open_GetVAs (n : nat) (t : typ) :
        option (OpenT ts tus tvs (typD ts t)) :=
        bind (m := option)
             (nth_error_get_hlist_nth (typD ts) tvs n)
             (fun t_get =>
                let '(existT t' get) := t_get in
                bind (m := option)
                     (type_cast ts t' t)
                     (fun cast =>
                        ret (fun us vs => Rcast_val cast (get vs)))).

    End OpenT.

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

    Definition func_simul ts (f : func) : option { t : typ & typD ts t } :=
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
                                                  end -> typD ts _
                                     with
                                       | eq_refl => fun x => type_weaken ts _ x
                                     end (symD f)))
      end eq_refl.

    Section exprD'.
      Variable ts : list Type.
      Variable tus : tenv typ.

      Fixpoint exprD' (tvs : tenv typ) (t : typ) (e : expr typ func)
      : option (OpenT ts tus tvs (typD ts t)) :=
        match e return option (OpenT ts tus tvs (typD ts t)) with
          | Var v => @Open_GetVAs ts tus tvs v t
          | Inj f =>
            match @funcAs _ f t with
              | None => None
              | Some val =>
                Some (@Open_Inj ts tus tvs _ val)
            end
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
          | UVar u => @Open_GetUAs ts tus tvs u t
        end
      with exprD'_simul (tvs : tenv typ) (e : expr typ func)
           : option { t : typ & OpenT ts tus tvs (typD ts t) } :=
             match e return option { t : typ & OpenT ts tus tvs (typD ts t) } with
               | Var v => @Open_UseV _ (typD ts) tus tvs v
               | Inj f =>
                 match @func_simul _ f with
                   | None => None
                   | Some (existT t val) =>
                     Some (@existT _ (fun t => OpenT ts tus tvs (typD ts t))
                                   t (fun _ _ => val))
                 end
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
               | UVar u => Open_UseU (typD ts) tus tvs u
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
             (exprD'_simul ts tus tvs x)
                 (fun t_x =>
                    let '(existT t' x) := t_x in
                    bind (m := option)
                         (exprD' ts tus tvs (typ_arr t' t) f)
                         (fun f => ret (@Open_App ts _ _ _ _ f x))).
    Proof. reflexivity. Qed.

    Lemma exprD'_simul_App'
    : forall ts tus tvs f x,
        exprD'_simul ts tus tvs (App f x) =
        bind (m := option)
                      (exprD'_simul ts tus tvs f)
                      (fun t_f =>
                         let '(existT t' f) := t_f in
                         arr_match (fun T =>
                                      OpenT ts tus tvs T ->
                                      option { t : typ & OpenT ts tus tvs (typD ts t) })
                                   ts t'
                                   (fun d r f =>
                                      bind (m := option)
                                           (exprD' ts tus tvs d x)
                                           (fun x =>
                                              ret (@existT _
                                                           (fun t => OpenT ts tus tvs (typD ts t))
                                                           r
                                                           (fun us vs => (f us vs) (x us vs)))))
                                   (fun _ => None)
                                   f).
    Proof. reflexivity. Qed.

    Lemma exprD'_Abs'
    : forall ts tus e tvs t' t,
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

    Lemma exprD'_simul_Abs'
    : forall ts tus e tvs t,
        exprD'_simul ts tus tvs (Abs t e) =
        bind (m := option)
             (exprD'_simul ts tus (t :: tvs) e)
             (fun t_val =>
                let '(existT t' f) := t_val in
                ret (@existT _ (fun t => OpenT ts tus tvs (typD ts t))
                             (typ_arr t t')
                             match eq_sym (typD_arr ts t t') in _ = T
                                   return OpenT ts tus tvs T
                             with
                               | eq_refl => fun us vs x => f us (Hcons x vs)
                             end)).
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

    Lemma exprD'_typeof_expr
    : forall ts tus e tvs t val,
        exprD' ts tus tvs t e = Some val \/
        exprD'_simul ts tus tvs e = Some (@existT _ _ t val) ->
        typeof_expr ts tus tvs e = Some t.
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
        { destruct (typ2_match_case ts x).
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
        { destruct (typ2_match_case ts t0).
          { destruct H0 as [ ? [ ? [ ? ? ] ] ].
            rewrite H0 in *.
            red in x1. subst. simpl in *.
            consider (exprD' ts tus (t :: tvs) x0 e); intros.
            { specialize (IHe _ _ _ (or_introl H)).
              rewrite IHe.
              consider (type_cast ts x t); intros.
              { red in r. subst; auto. }
              { exfalso. clear - H2.
                destruct (eq_sym (typ2_cast ts x x0)).
                congruence. } }
            { exfalso. clear - H1. destruct (eq_sym (typ2_cast ts x x0)).
              destruct (type_cast ts x t); congruence. } }
          { rewrite H0 in H. congruence. } }
        { simpl in *. forward.
          specialize (IHe _ _ _ (or_intror H0)).
          rewrite IHe. inv_all; subst. auto. } }
      { unfold exprD'_simul, exprD', Open_GetUAs, Open_UseU in *. simpl in *.
        destruct H; forward; inv_all; subst;
        eapply nth_error_get_hlist_nth_Some in H0; destruct H0; auto.
        red in r. subst. auto. }
    Qed.

    Lemma exprD'_deterministic
    : forall ts tus e tvs t1 t2 val val',
        exprD' ts tus tvs t1 e = Some val ->
        exprD' ts tus tvs t2 e = Some val' ->
        Rty ts t1 t2.
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
        destruct (typ2_match_case ts t1).
        { destruct (typ2_match_case ts t2).
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
      { unfold exprD', Open_GetUAs in *. simpl in *.
        forward; inv_all; subst. }
    Qed.

    (** NOTE: These are requiring decidable equality **)
    Local Instance RelDec_eq_typ : RelDec (@eq typ) := RelDec_Rty nil.
    Local Instance RelDecCorrect_eq_typ : RelDec_Correct RelDec_eq_typ :=
      _.

    Lemma exprD_simul'
    : forall ts tus e tvs tv,
        exprD'_simul ts tus tvs e = Some tv <->
        (typeof_expr ts tus tvs e = Some (projT1 tv) /\
         exprD' ts tus tvs (projT1 tv) e = Some (projT2 tv)).
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
          destruct (typ2_match_case ts x).
          { destruct H3 as [ ? [ ? [ ? ? ] ] ].
            unfold type_of_apply.
            unfold Rty in *. subst. simpl in *.
            rewrite H3 in H1.
            destruct tv; simpl in *.
            consider (exprD'_simul ts tus tvs e2); intros.
            { destruct s. specialize (proj1 (IHe2 _) eq_refl); clear IHe2.
              simpl in *. intros. forward_reason.
              Cases.rewrite_all_goal. simpl in *.
              consider (exprD' ts tus tvs x0 e2).
              { intros.
                unfold Open_App in *. clear H3.
                specialize (exprD'_deterministic _ _ _ H1 H6).
                unfold Rty. intros; subst.
                assert (x1 = x).
                { clear - H7. destruct (eq_sym (typ2_cast ts x2 x1)).
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
                destruct (eq_sym (typ2_cast ts x0 x1)).
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
          destruct (typ2_match_case ts t).
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
            generalize (typ2_cast ts x x0). intro.
            unfold typ_arr in *.
            generalize dependent (typD ts (typ2 x x0)).
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
          consider (exprD' ts tus (t :: tvs) t0 e).
          { intros.
            rewrite eq_option_eq in H1. inv_all; subst.
            specialize (IHe (@existT _ _ t0 o0)).
            simpl in *. destruct IHe; forward_reason.
            Cases.rewrite_all_goal.
            unfold Rcast_val. reflexivity. }
          { intros. exfalso. clear - H1.
            destruct (eq_sym (typ2_cast ts t t0)). congruence. } } }
      { unfold exprD', exprD'_simul, Open_UseU, Open_GetUAs. simpl. intros.
        forward; inv_all; subst; simpl.
        eapply nth_error_get_hlist_nth_Some in H0. simpl in *.
        destruct H0.
        rewrite x0. destruct tv. simpl in *.
        split; intros.
        { inv_all. subst. rewrite type_cast_refl; eauto. subst; auto. }
        { destruct H0. inv_all; subst.
          rewrite type_cast_refl in H1; eauto. inv_all; subst.
          reflexivity. } }
    Qed.

    Theorem exprD'_App
    : (* RTypeOk _ -> Typ2Ok Typ2_Fun -> RSymOk RSym_func -> *)
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
    Proof.
      simpl. intros.
      rewrite exprD'_App'. simpl.
      consider (exprD'_simul ts tus tvs x); intros.
      { destruct s.
        generalize (@exprD'_typeof_expr ts tus x tvs _ _ (or_intror H)).
        intros. rewrite H0.
        forward.
        eapply exprD_simul' in H.
        simpl in *. destruct H.
        rewrite H2. reflexivity. }
      { consider (typeof_expr ts tus tvs x); auto; intros.
        consider (exprD' ts tus tvs (typ_arr t0 t) f); auto; intros.
        consider (exprD' ts tus tvs t0 x); auto; intros.
        exfalso.
        assert (exprD'_simul ts tus tvs x = Some (@existT _ _ t0 o0)).
        rewrite exprD_simul'. split; auto.
        congruence. }
    Qed.


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
