Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.AbsAppI.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprDI.

Set Implicit Arguments.
Set Strict Implicit.

Module ExprDenote <: ExprDenote.

  Section with_types.
    Context {typ : Type}.
    Context {func : Type}.
    Context {RType_typD : RType typ}.
    Context {Typ2_Fun : Typ2 _ RFun}.
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

    Section exprT.
      Variables tus tvs : tenv typ.

      (** Auxiliary definitions **)
      Definition exprT_GetUAs (n : nat) (t : typ) :
        option (exprT tus tvs (typD t)) :=
        match nth_error_get_hlist_nth typD tus n with
        | Some (existT _ t' get) =>
          match type_cast t' t with
          | Some cast => Some (fun us vs => Rcast_val cast (get us))
          | _ => None
          end
        | _ => None
        end.

      Definition exprT_GetVAs (n : nat) (t : typ) :
        option (exprT tus tvs (typD t)) :=
        match nth_error_get_hlist_nth typD tvs n with
        | Some (existT _ t' get) =>
          match type_cast t' t with
          | Some cast => Some (fun us vs => Rcast_val cast (get vs))
          | _ => None
          end
        | _ => None
        end.

    End exprT.

    Definition func_simul (f : func) : option { t : typ & typD t } :=
      match typeof_sym f as Z
            return Z = typeof_sym (RSym:=RSym_func) f -> option _
      with
        | None => fun _ => None
        | Some T => fun pf =>
          Some (@existT _ _ T
                        (match pf in _ = Z
                               return match Z with
                                      | Some t => typD t
                                      | None => unit:Type
                                      end -> typD _
                         with
                         | eq_refl => fun x => x
                         end (symD f)))
      end eq_refl.

    Section exprD'.
      Variable tus : tenv typ.

      Fixpoint exprD' (tvs : tenv typ) (t : typ) (e : expr typ func)
      : option (exprT tus tvs (typD t)) :=
        match e return option (exprT tus tvs (typD t)) with
          | Var v => @exprT_GetVAs tus tvs v t
          | Inj f =>
            match @symAs _ _ _ _ f t with
              | None => None
              | Some val =>
                Some (exprT_Inj tus tvs val)
            end
          | App f x =>
            match exprD'_simul tvs x with
              | None => None
              | Some (existT _ t' x) =>
                match exprD' tvs (typ_arr t' t) f with
                  | None => None
                  | Some f => Some (exprT_App f x)
                end
            end
          | Abs t' e =>
            arr_match (fun T => option (exprT tus tvs T)) t
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
          | UVar u => @exprT_GetUAs tus tvs u t
        end
      with exprD'_simul (tvs : tenv typ) (e : expr typ func)
      : option { t : typ & exprT tus tvs (typD t) } :=
        match e return option { t : typ & exprT tus tvs (typD t) } with
          | Var v => exprT_UseV tus tvs v
          | Inj f =>
            match @func_simul f with
              | None => None
              | Some (existT _ t val) =>
                Some (@existT _ (fun t => exprT tus tvs (typD t))
                              t (fun _ _ => val))
            end
          | App f x =>
            match exprD'_simul tvs f with
              | None => None
              | Some (existT _ t' f) =>
                arr_match (fun T =>
                             exprT tus tvs T ->
                             option { t : typ & exprT tus tvs (typD t) })
                          t'
                          (fun d r f =>
                             match exprD' tvs d x with
                               | None => None
                               | Some x =>
                                 Some (@existT _
                                               (fun t => exprT tus tvs (typD t))
                                               r
                                               (fun us vs => (f us vs) (x us vs)))
                             end)
                          (fun _ => None)
                          f
            end
          | Abs t e =>
            match exprD'_simul (t :: tvs) e with
              | None => None
              | Some (existT _ t' f) =>
                Some (@existT _ (fun t => exprT tus tvs (typD t))
                              (typ_arr t t')
                              match eq_sym (typD_arr t t') in _ = T
                                    return exprT tus tvs T
                              with
                                | eq_refl => fun us vs x => f us (Hcons x vs)
                              end)
            end
          | UVar u => exprT_UseU tus tvs u
        end.
    End exprD'.

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


    (** Equations **)
    Theorem exprD'_Var
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
    Proof. reflexivity. Qed.

    Theorem exprD'_UVar
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
    Proof. reflexivity. Qed.

    Theorem exprD'_Inj
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall tus tvs t s,
        exprD' tus tvs t (Inj s) =
        match symAs s t with
        | Some val => Some (fun _ _ => val)
        | _ => None
        end.
    Proof. reflexivity. Qed.

    Lemma exprD'_App'
    : forall tus tvs t f x,
        exprD' tus tvs t (App f x) =
        match exprD'_simul tus tvs x with
        | Some (existT _ t' x) =>
          match exprD' tus tvs (typ_arr t' t) f with
          | Some f => Some (exprT_App f x)
          | _ => None
          end
        | _ => None
        end.
    Proof. reflexivity. Qed.

    Lemma exprD'_simul_App'
    : forall tus tvs f x,
        exprD'_simul tus tvs (App f x) =
        match exprD'_simul tus tvs f with
        | Some (existT _ t' f) =>
          arr_match (fun T =>
                       exprT tus tvs T ->
                       option { t : typ & exprT tus tvs (typD t) })
                    t'
                    (fun d r f =>
                       match exprD' tus tvs d x with
                       | Some x =>
                         Some (@existT _
                                       (fun t => exprT tus tvs (typD t))
                                       r
                                       (fun us vs => (f us vs) (x us vs)))
                       | _ => None
                       end)
                    (fun _ => None)
                    f
        | _ => None
        end.
    Proof. reflexivity. Qed.

    Lemma exprD'_Abs'
    : forall tus e tvs t' t,
        exprD' tus tvs t (Abs t' e) =
        arr_match (fun T => option (exprT tus tvs T)) t
                  (fun d r =>
                     match type_cast d t'
                         , exprD' tus (t' :: tvs) r e
                     with
                     | Some cast , Some val =>
                       Some (fun us vs x =>
                               val us (Hcons (Rcast_val cast x) vs))
                     | _ , _ => None
                     end)
                  None.
    Proof. reflexivity. Qed.

    Lemma exprD'_simul_Abs'
    : forall tus e tvs t,
        exprD'_simul tus tvs (Abs t e) =
        match exprD'_simul tus (t :: tvs) e with
        | Some (existT _ t' f) =>
          Some (@existT _ (fun t => exprT tus tvs (typD t))
                        (typ_arr t t')
                        match eq_sym (typD_arr t t') in _ = T
                              return exprT tus tvs T
                        with
                        | eq_refl => fun us vs x => f us (Hcons x vs)
                        end)
        | _ => None
        end.
    Proof. reflexivity. Qed.

    Theorem exprD'_Abs
    : RTypeOk -> Typ2Ok Typ2_Fun -> RSymOk RSym_func ->
      forall tus tvs t t' e,
        exprD' tus tvs t (Abs t' e) =
        arr_match (fun T => option (exprT tus tvs T)) t
                  (fun d r =>
                     match type_cast d t'
                         , exprD' tus (t' :: tvs) r e
                     with
                     | Some cast , Some val =>
                       Some (fun us vs x =>
                               val us (Hcons (Rcast_val cast x) vs))
                     | _ , _ => None
                     end)
                  None.
    Proof. reflexivity. Qed.

    Lemma exprD'_typeof_expr
    : forall tus e tvs t val,
        exprD' tus tvs t e = Some val \/
        exprD'_simul tus tvs e = Some (@existT _ _ t val) ->
        typeof_expr tus tvs e = Some t.
    Proof.
      induction e; simpl; intros.
      { unfold exprD', exprD'_simul, exprT_GetVAs, exprT_UseV in *. simpl in *.
        destruct H; forward; inv_all; subst;
        eapply nth_error_get_hlist_nth_Some in H0; destruct H0; simpl in *; auto.
        red in r. subst. auto. }
      { unfold exprD', exprD'_simul, func_simul, symAs in *; simpl in *.
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
          unfold arr_match. rewrite typ2_match_iota; eauto.
          rewrite type_cast_refl; eauto.
          rewrite eq_Const_eq. reflexivity. }
        { destruct (typ2_match_case x).
          { destruct H as [ ? [ ? [ ? ? ] ] ].
            rewrite H in *.
            specialize (IHe1 _ _ _ (or_intror H0)).
            red in x2. subst. simpl in *.
            Require Import MirrorCore.Util.Compat.
            autorewrite_with_eq_rw_in H1.
            forward. inv_all; subst.
            specialize (IHe2 _ _ _ (or_introl _ H1)).
            rewrite IHe2. subst.
            unfold type_of_apply. rewrite H.
            rewrite type_cast_refl; eauto. simpl. revert H2.
            do 2 rewrite eq_Const_eq.
            intro. inv_all. subst.
            reflexivity. }
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
      { unfold exprD'_simul, exprD', exprT_GetUAs, exprT_UseU in *. simpl in *.
        destruct H; forward; inv_all; subst;
        eapply nth_error_get_hlist_nth_Some in H0; destruct H0; auto.
        red in r. subst. auto. }
    Qed.

    Lemma exprD'_deterministic
    : forall tus e tvs t1 t2 val val',
        exprD' tus tvs t1 e = Some val ->
        exprD' tus tvs t2 e = Some val' ->
        Rty t1 t2.
    Proof.
      induction e; simpl; intros; red.
      { unfold exprD', exprT_GetVAs in *. simpl in *.
        forward; inv_all; subst. }
      { unfold exprD' in *; simpl in *. forward; inv_all; subst.
        unfold symAs in *.
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
      { unfold exprD', exprT_GetUAs in *. simpl in *.
        forward; inv_all; subst. }
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
      { unfold exprD'_simul, exprD', exprT_UseV, exprT_GetVAs. simpl. intros.
        forward; inv_all; subst; simpl.
        eapply nth_error_get_hlist_nth_Some in H0. simpl in *.
        destruct H0.
        rewrite x0. destruct tv. simpl in *.
        split; intros.
        { inv_all. subst. rewrite type_cast_refl; eauto. subst; auto. }
        { destruct H0. inv_all; subst.
          rewrite type_cast_refl in H1; eauto. inv_all; subst.
          eauto. } }
      { unfold exprD', exprD'_simul,func_simul, symAs. simpl in *; intros.
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
                unfold exprT_App in *. clear H3.
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
                  autorewrite_with_eq_rw_in H7.
                  autorewrite_with_eq_rw.
                  rewrite H6 in H1.
                  inv_all. subst. reflexivity. } }
              { intros. exfalso. clear - H7.
                destruct (eq_sym (typ2_cast x0 x1)).
                congruence. } }
            { exfalso.
              autorewrite_with_eq_rw_in H1.
              forward. inv_all. subst. subst.
              specialize (H5 (@existT _ _ x0 e3)); simpl in *.
              rewrite H1 in *.
              erewrite exprD'_typeof_expr in H5.
              2: eauto.
              autorewrite_with_eq_rw_in H6.
              destruct H5.
              assert (Some x0 = Some x0 /\ Some e3 = Some e3); auto.
              apply H7 in H8. congruence. } }
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
            specialize (IHe1 (@existT _ _ (typ_arr x x0) e0)).
            simpl in *. destruct IHe1. forward_reason.
            rewrite H8. rewrite H0.
            autorewrite_with_eq_rw.
            Cases.rewrite_all_goal. f_equal. f_equal. subst.
            unfold exprT_App. clear.
            generalize (typ2_cast x x0). intro.
            unfold typ_arr in *.
            generalize dependent (typD (typ2 x x0)).
            intros. revert e0. clear. subst. auto. }
          { rewrite H0 in H5. congruence. } } }
      { intros. rewrite exprD'_Abs, exprD'_simul_Abs'; eauto.
        unfold typ_arr, arr_match in *.
        simpl; split; intros; forward; inv_all; subst; simpl in *.
        { eapply IHe in H0. forward_reason. simpl in *.
          Cases.rewrite_all_goal. split; auto.
          rewrite typ2_match_iota; auto.
          rewrite type_cast_refl; eauto.
          Cases.rewrite_all_goal.
          unfold Rcast_val.
          rewrite eq_option_eq. reflexivity. }
        { forward_reason; inv_all; subst.
          destruct tv; simpl in *; subst.
          rewrite typ2_match_iota in H1; eauto.
          rewrite type_cast_refl in *; eauto.
          specialize (IHe (t :: tvs)).
          consider (exprD' tus (t :: tvs) t0 e).
          { intros.
            rewrite eq_option_eq in H1. inv_all; subst.
            specialize (IHe (@existT _ _ t0 e1)).
            simpl in *. destruct IHe; forward_reason.
            Cases.rewrite_all_goal.
            unfold Rcast_val. reflexivity. }
          { intros. exfalso. clear - H1.
            destruct (eq_sym (typ2_cast t t0)). congruence. } } }
      { unfold exprD', exprD'_simul, exprT_UseU, exprT_GetUAs. simpl. intros.
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
        | _ => None
        end.
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
        assert (exprD'_simul tus tvs x = Some (@existT _ _ t0 e0)).
        rewrite exprD_simul'. split; auto.
        congruence. }
    Qed.

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
