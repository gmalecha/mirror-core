Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Lambda2.TypesI2.
Require Import MirrorCore.Lambda2.ExprCore.

Set Implicit Arguments.
Set Strict Implicit.

Module Type ExprDenote_core.

  Section with_types.
    Context {typ : Type}.
    Context {typD : typ -> Type}.
    Context {func : Type}.

    Let Rty := @eq typ.

    Variable type_cast : forall a b, option (Rty a b).
    Variable typ_arr : typ -> typ -> typ.
    Variable arr_match : forall (T : Type -> Type) t,
                           (forall a b, T (typD a -> typD b)) ->
                           T (typD t) ->
                           T (typD t).

    Hypothesis typD_arr : forall a b, typD (typ_arr a b) = (typD a -> typD b).
    Variable typeof_func : func -> option typ.
    Variable funcD : forall f, match typeof_func f with
                                 | None => unit
                                 | Some t => typD t
                               end.

    Definition Rcast T {a b} (pf : Rty a b) : T (typD a) -> T (typD b) :=
      match pf in _ = t return T (typD a) -> T (typD t) with
        | eq_refl => fun x => x
      end.

    Definition Rcast_val : forall {a b} (pf : Rty a b), typD a -> typD b :=
      @Rcast (fun T => T).

    Section OpenT.
      Variables tus tvs : tenv typ.

      Definition OpenT (T : Type) :=
        hlist typD tus -> hlist typD tvs -> T.

      Definition Open_UseV (n : nat) : option { t : typ & OpenT (typD t) } :=
        bind (m := option)
             (nth_error_get_hlist_nth _ tvs n)
             (fun t_get =>
                let '(existT t get) := t_get in
                ret (@existT _ (fun t => OpenT (typD t)) t
                             (fun us vs => get vs))).

      Definition Open_UseU (n : nat) : option { t : typ & OpenT (typD t) } :=
        bind (m := option)
             (nth_error_get_hlist_nth _ tus n)
             (fun t_get =>
                let '(existT t get) := t_get in
                ret (@existT _ (fun t => OpenT (typD t)) t
                             (fun us vs => get us))).

      Definition Open_App {t u}
      : OpenT (typD (typ_arr t u)) -> OpenT (typD t) -> OpenT (typD u) :=
        match eq_sym (typD_arr t u) in _ = T
              return OpenT T -> OpenT (typD t) -> OpenT (typD u)
        with
          | eq_refl => fun f x => fun us vs => (f us vs) (x us vs)
        end.

      Definition Open_Inj {t} (val : typD t)
      : OpenT (typD t) :=
        fun _ _ => val.


      (** Auxiliary definitions **)
      Definition Open_GetUAs (n : nat) (t : typ) :
        option (OpenT (typD t)) :=
        bind (m := option)
             (nth_error_get_hlist_nth typD tus n)
             (fun t_get =>
                let '(existT t' get) := t_get in
                bind (m := option)
                     (type_cast t' t)
                     (fun cast =>
                        ret (fun us vs => Rcast_val cast (get us)))).

      Definition Open_GetVAs (n : nat) (t : typ) :
        option (OpenT (typD t)) :=
        bind (m := option)
             (nth_error_get_hlist_nth typD tvs n)
             (fun t_get =>
                let '(existT t' get) := t_get in
                bind (m := option)
                     (type_cast t' t)
                     (fun cast =>
                        ret (fun us vs => Rcast_val cast (get vs)))).

    End OpenT.

    Definition Open_Abs {tus tvs t u}
    : OpenT tus (t :: tvs) (typD u) -> OpenT tus tvs (typD (typ_arr t u)) :=
      match eq_sym (typD_arr t u) in _ = T
            return OpenT tus (t :: tvs) (typD u) -> OpenT tus tvs T
      with
        | eq_refl => fun f => fun us vs x => f us (Hcons x vs)
      end.

    Definition funcAs (f : func) (t : typ) : option (typD t) :=
      match typeof_func f as Z
            return Z = typeof_func f -> option (typD t)
      with
        | None => fun _ => None
        | Some T => fun pf =>
                      match type_cast T t with
                        | None => None
                        | Some cast =>
                          match cast in _ = X return option (typD X) with
                            | eq_refl =>
                              Some (match pf in _ = Z
                                          return match Z with
                                                   | Some t => typD t
                                                   | None => unit
                                                 end -> typD _
                                    with
                                      | eq_refl => fun x => x
                                    end (funcD f))
                          end
                      end
      end eq_refl.

    Definition func_simul (f : func) : option { t : typ & typD t } :=
      match typeof_func f as Z
            return Z = typeof_func f -> option _
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
                                     end (funcD f)))
      end eq_refl.


    Fixpoint exprD' (tus tvs : tenv typ) (t : typ) (e : expr typ func)
    : option (OpenT tus tvs (typD t)) :=
      match e return option (OpenT tus tvs (typD t)) with
        | Var v => Open_GetVAs tus tvs v t
        | Inj f =>
          bind (m := option)
               (funcAs f t)
               (fun val =>
                  ret (@Open_Inj tus tvs t val))
        | App f x =>
          bind (m := option)
               (exprD'_simul tus tvs x)
               (fun t_x =>
                  let '(existT t' x) := t_x in
                  bind (m := option)
                       (exprD' tus tvs (typ_arr t' t) f)
                       (fun f => ret (@Open_App _ _ _ _ f x)))
        | Abs t' e =>
          (** TODO: This should be abstract **)
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
                    None
        | UVar u => Open_GetUAs tus tvs u t
      end
    with exprD'_simul (tus tvs : tenv typ) (e : expr typ func)
    : option { t : typ & OpenT tus tvs (typD t) } :=
      match e return option { t : typ & OpenT tus tvs (typD t) } with
        | Var v => @Open_UseV tus tvs v
        | Inj f =>
          bind (func_simul f)
               (fun t_val =>
                  let '(existT t val) := t_val in
                  ret (@existT _ (fun t => OpenT tus tvs (typD t))
                               t (fun _ _ => val)))
        | App f x =>
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
                            f)
        | Abs t e =>
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
                                end))
        | UVar u => @Open_UseU tus tvs u
      end.

    Theorem exprD'_respects
    : forall tus tvs t t' e (pf : Rty t' t),
        exprD' tus tvs t e =
        Rcast (fun T => option (OpenT tus tvs T)) pf (exprD' tus tvs t' e).
    Proof.
      destruct pf. reflexivity.
    Qed.

    Theorem exprD'_Abs
    : forall us ve t e u,
        exprD' us ve u (Abs t e) =
        arr_match (fun T => option (OpenT us ve T))
                  u
                  (fun l r =>
                     match type_cast l t
                         , exprD' us (t :: ve) r e
                     with
                       | Some cast , Some f =>
                         Some (fun u g => fun x =>
                                            f u (Hcons (F := typD)
                                                       (Rcast_val cast x) g))
                       | _ , _ => None
                     end)
                  None.
    Proof. reflexivity. Qed.

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
        | Inj f => typeof_func f
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

    Definition exprD'_simpl (tus tvs : tenv typ) (t : typ) (e : expr typ func)
    : option (OpenT tus tvs (typD t)) :=
      match e with
        | Var v =>
          bind (m := option)
               (nth_error_get_hlist_nth typD tvs v)
               (fun t_get =>
                  let '(existT t' get) := t_get in
                  bind (m := option)
                       (type_cast t' t)
                       (fun cast =>
                          ret (fun us vs => Rcast_val cast (get vs))))
        | Inj f =>
          bind (m := option)
               (funcAs f t)
               (fun val =>
                  ret (fun _ _ => val))
        | App f x =>
          bind (m := option)
              (typeof_expr tus tvs x)
              (fun t' =>
                 bind (exprD' tus tvs (typ_arr t' t) f)
                      (fun f =>
                         bind (exprD' tus tvs t' x)
                              (fun x =>
                                 ret (Open_App f x))))
        | Abs t' e =>
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
                    None
        | UVar u =>
          bind (m := option)
               (nth_error_get_hlist_nth typD tus u)
               (fun t_get =>
                  let '(existT t' get) := t_get in
                  bind (m := option)
                       (type_cast t' t)
                       (fun cast =>
                          ret (fun us vs => Rcast_val cast (get us))))
      end.

    Axiom type_cast_refl : forall x, type_cast x x = Some eq_refl.
    Axiom type_cast_total : forall x y, type_cast x y = None <-> ~Rty x y.

    Global Instance RelDec_Rty : RelDec Rty :=
    { rel_dec := fun a b => match type_cast a b with
                              | Some _ => true
                              | None => false
                            end }.

    Global Instance RelDec_Correct_Rty : @RelDec_Correct _ Rty _.
    Proof.
      constructor. unfold rel_dec; simpl.
      clear. intros; consider (type_cast x y); intros.
      split; auto. apply type_cast_total in H. intuition.
    Qed.

    Axiom arr_match_case
    : forall x,
        (exists d r (pf : Rty x (typ_arr d r)),
           forall T tr fa,
             arr_match T x tr fa =
             match eq_sym pf in _ = t return T (typD t) with
               | eq_refl => match eq_sym (typD_arr d r) in _ = t return T t with
                              | eq_refl => tr d r
                            end
             end) \/
        (forall T tr fa, arr_match T x tr fa = fa).

    Axiom Rty_typ_arr : forall a b c d,
                          Rty (typ_arr a b) (typ_arr c d) <->
                          Rty c a /\ Rty b d.


    Lemma exprD'_deterministic
    : forall tus e tvs t1 t2 val val',
        exprD' tus tvs t1 e = Some val ->
        exprD' tus tvs t2 e = Some val' ->
        Rty t1 t2.
    Proof.
      induction e; simpl; intros; red.
      { admit. }
      { admit. }
      { forward. inv_all; subst.
        specialize (IHe1 _ _ _ _ _ H2 H1).
        eapply Rty_typ_arr in IHe1. destruct IHe1.
        destruct H3. reflexivity. }
      { destruct (arr_match_case t1).
        { destruct (arr_match_case t2).
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
            subst. reflexivity. }
          { rewrite H2 in *; congruence. } }
        { rewrite H1 in *. congruence. } }
      { admit. }
    Qed.

    (** TODO: Move to ExtLib, these are like Iso **)
    Lemma eq_CoFunctor
    : forall T (a b : T) (pf : a = b) (F G : T -> Type) val x,
        match pf in _ = x return F x -> G x with
          | eq_refl => val
        end x =
        match pf in _ = x return G x with
          | eq_refl => val match eq_sym pf in _ = x return F x with
                             | eq_refl => x
                           end
        end.
    Proof.
      clear. destruct pf. reflexivity.
    Qed.

    Lemma eq_Const
    : forall T (a b : T) (pf : a = b) (R : Type) val,
        match pf in _ = x return R with
          | eq_refl => val
        end = val.
    Proof.
      clear. destruct pf. reflexivity.
    Qed.

    Lemma eq_option
    : forall T (a b : T) (pf : a = b) (F : _ -> Type) val,
        match pf in _ = x return option (F x) with
          | eq_refl => val
        end = match val with
                | None => None
                | Some val => Some match pf in _ = x return F x with
                                     | eq_refl => val
                                   end
              end.
    Proof.
      clear. destruct pf. destruct val; reflexivity.
    Qed.


    Lemma exprD_simul'
    : forall tus e tvs tv,
        exprD'_simul tus tvs e = Some tv <->
        (typeof_expr tus tvs e = Some (projT1 tv) /\
         exprD' tus tvs (projT1 tv) e = Some (projT2 tv)).
    Proof.
      induction e; simpl.
      { unfold Open_UseV, Open_GetVAs. simpl. intros.
        forward; inv_all; subst; simpl.
        eapply nth_error_get_hlist_nth_Some in H0. simpl in *.
        destruct H0.
        rewrite x0. destruct tv. simpl in *.
        split; intros.
        { inv_all. subst. rewrite type_cast_refl. subst; auto. }
        { destruct H0. inv_all; subst.
          rewrite type_cast_refl in H1. inv_all; subst. auto. } }
      { unfold func_simul, funcAs. intros.
        generalize (funcD f).
        destruct (typeof_func f).
        { split; intros; forward; inv_all; subst; simpl.
          rewrite type_cast_refl. intuition.
          red in r. subst. destruct H0. destruct tv.
          simpl in *; forward; inv_all; subst.
          auto. }
        { intuition congruence. } }
      { intros. specialize (@IHe1 tvs).
        specialize (IHe2 tvs).
        split; intros.
        { forward; inv_all; subst; simpl.
          specialize (proj1 (IHe1 _) eq_refl); clear IHe1.
          intros. forward_reason.
          Cases.rewrite_all_goal. simpl in *.
          destruct (arr_match_case x).
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
                specialize (exprD'_deterministic _ H1 H6).
                unfold Rty. intros; subst.
                assert (x1 = x).
                { clear - H7. destruct (eq_sym (typD_arr x2 x1)).
                  inv_all. auto. }
                subst. Cases.rewrite_all_goal.
                rewrite type_cast_refl. split; auto.
                f_equal.
                repeat rewrite eq_CoFunctor in *.
                repeat rewrite eq_Const in *.
                rewrite H6 in H1.
                inversion H7; clear H7; subst.
                inversion H1; clear H1; subst.
                clear - H8. inv_all.
                admit. }
              { intros. exfalso. clear - H7.
                destruct (eq_sym (typD_arr x0 x1)).
                congruence. } }
            { exfalso. admit. } }
          { rewrite H3 in H1. congruence. } }
        { destruct H. forward; inv_all; subst.
          specialize (proj1 (IHe2 _) eq_refl); clear IHe2.
          intros; forward_reason; inv_all; subst; simpl in *.
          unfold type_of_apply in *.
          destruct (arr_match_case t).
          { destruct H0 as [ ? [ ? [ ? ? ] ] ].
            rewrite H0 in H5.
            red in x2. subst; simpl in *.
            rewrite eq_Const in H5. forward.
            red in r. inv_all; subst.
            destruct tv; simpl in *.
            specialize (IHe1 (@existT _ _ (typ_arr x x0) o0)).
            simpl in *. destruct IHe1. forward_reason.
            rewrite H8. rewrite H0.
            repeat (rewrite eq_CoFunctor; rewrite eq_Const).
            Cases.rewrite_all_goal. f_equal. f_equal. subst.
            unfold Open_App. clear.
            generalize (typD_arr x x0). intro.
            generalize dependent (typD (typ_arr x x0)).
            intros. revert o0. clear. subst. auto. }
          { rewrite H0 in H5. congruence. } } }
      { simpl; split; intros; forward; inv_all; subst; simpl in *.
        { eapply IHe in H0. forward_reason. simpl in *.
          Cases.rewrite_all_goal. split; auto.
          Axiom arr_match_typ_arr : forall a b T tr fa,
                                      arr_match T (typ_arr a b) tr fa =
                                      match eq_sym (typD_arr a b) in _ = t return T t with
                                        | eq_refl => tr a b
                                      end.
          rewrite arr_match_typ_arr.
          rewrite type_cast_refl.
          Cases.rewrite_all_goal.
          simpl. auto. }
        { forward_reason; inv_all; subst.
          destruct tv; simpl in *; subst.
          rewrite arr_match_typ_arr in H1.
          rewrite type_cast_refl in *.
          specialize (IHe (t :: tvs)).
          consider (exprD' tus (t :: tvs) t0 e).
          { intros.
            rewrite eq_option in H1. inv_all; subst.
            specialize (IHe (@existT _ _ t0 o0)).
            simpl in *. destruct IHe; forward_reason.
            Cases.rewrite_all_goal. auto. }
          { intros. exfalso. clear - H1.
            destruct (eq_sym (typD_arr t t0)). congruence. } } }
      { unfold Open_UseU, Open_GetUAs. simpl. intros.
        forward; inv_all; subst; simpl.
        eapply nth_error_get_hlist_nth_Some in H0. simpl in *.
        destruct H0.
        rewrite x0. destruct tv. simpl in *.
        split; intros.
        { inv_all. subst. rewrite type_cast_refl. subst; auto. }
        { destruct H0. inv_all; subst.
          rewrite type_cast_refl in H1. inv_all; subst. auto. } }
    Qed.

    Theorem exprD'_exprD'_simpl
    : forall tus e tvs t,
        exprD' tus tvs t e = exprD'_simpl tus tvs t e.
    Proof.
      induction e; simpl; intros; auto.
      { consider (exprD'_simul tus tvs e2); intros.
        { eapply exprD_simul' in H. destruct H.
          destruct s; simpl in *.
          Cases.rewrite_all_goal. auto. }
        { consider (typeof_expr tus tvs e2); intros; auto.
          consider (exprD' tus tvs t0 e2); intros; auto.
          destruct (@exprD_simul' tus e2 tvs (@existT _ _ t0 o)).
          simpl in *. forward_reason. congruence.
          forward; auto. } }
    Qed.

    Lemma arr_match_test_None
    : forall F x tr val,
        arr_match (fun x => option (F x)) x tr None = Some val ->
        exists d r (pf : Rty x (typ_arr d r)),
          Some val = match eq_sym pf in _ = t return option (F (typD t)) with
                       | eq_refl =>
                         match eq_sym (typD_arr d r) in _ = T return option (F T)
                         with
                           | eq_refl => tr d r
                         end
                     end.
    Proof.
      intros.
      destruct (arr_match_case x).
      { destruct H0 as [ ? [ ? [ ? ? ] ] ].
        rewrite H0 in H. exists x0; exists x1; exists x2.
        auto. }
      { rewrite H0 in H. congruence. }
    Qed.

    Theorem exprD'_weaken
    : forall tus e tvs t val,
        exprD' tus tvs t e = Some val ->
        forall tus' tvs',
          exists val',
            exprD' (tus ++ tus') (tvs ++ tvs') t e = Some val' /\
            forall us vs us' vs',
              val us vs = val' (hlist_app us us') (hlist_app vs vs').
    Proof.
      induction e; intros; repeat rewrite exprD'_exprD'_simpl in *;
      simpl exprD'_simpl in *.
      { forward; inv_all; subst.
        eapply nth_error_get_hlist_nth_weaken in H0.
        destruct H0 as [ ? [ ? ? ] ].
        rewrite H. simpl. rewrite H1.
        eexists; split; eauto.
        simpl in *. intros.
        unfold Rcast_val. unfold Rcast. destruct r. auto. }
      { forward. inv_all; subst. eexists; split; eauto. }
      { forward; inv_all; subst.
        Lemma typeof_expr_weaken
        : forall tus e tvs t,
            typeof_expr tus tvs e = Some t ->
            forall tus' tvs',
              typeof_expr (tus ++ tus') (tvs ++ tvs') e = Some t.
        Proof.
          induction e; simpl; intros; auto using ListNth.nth_error_weaken.
          { forward. Cases.rewrite_all_goal. auto. }
          { forward. eapply IHe in H. simpl in H. rewrite H. auto. }
        Qed.
        eapply typeof_expr_weaken in H.
        rewrite H.
        eapply IHe1 in H0. destruct H0 as [ ? [ ? ? ] ].
        rewrite H0.
        eapply IHe2 in H1. destruct H1 as [ ? [ ? ? ] ].
        rewrite H1. eexists; split; eauto.
        unfold Open_App.
        intros.
        repeat (rewrite eq_CoFunctor; rewrite eq_Const).
        rewrite <- H3.
        match goal with
          | |- match ?X with _ => _ end _ _ _ = _ =>
            generalize X
        end.
        clear - H2.
        generalize dependent (typD (typ_arr t0 t)).
        intros; subst. rewrite <- H2. reflexivity. }
      { destruct (arr_match_case t0).
        { destruct H0 as [ ? [ ? [ ? ? ] ] ].
          rewrite H0 in *; clear H0.
          red in x1. subst. simpl in *.
          repeat first [ rewrite eq_option in *
                       | rewrite eq_CoFunctor in *
                       | rewrite eq_Const in * ].
          forward; inv_all; subst.
          eapply IHe in H1.
          destruct H1 as [ ? [ ? ? ] ].
          simpl in H0. rewrite H0.
          eexists; split; eauto.
          intros.
          unfold OpenT.
          repeat first [ rewrite eq_option in *
                       | rewrite eq_CoFunctor in *
                       | rewrite eq_Const in * ].
          revert H1. clear. simpl in *.
          destruct (eq_sym (typD_arr x x0)).
          intros. eapply FunctionalExtensionality.functional_extensionality.
          intros. specialize (H1 us (Hcons (Rcast_val r x2) vs)).
          simpl in *. auto. }
        { rewrite H0 in H. congruence. } }
      { forward; inv_all; subst.
        eapply nth_error_get_hlist_nth_weaken in H0.
        destruct H0 as [ ? [ ? ? ] ].
        rewrite H. simpl. rewrite H1.
        eexists; split; eauto.
        simpl in *. intros.
        unfold Rcast_val. unfold Rcast. destruct r. auto. }
    Qed.
  End with_types.

End ExprDenote_core.

(*
Module Type ExprDenote.
  Include ExprDenote_core.

  Section with_types.
    Context {typ : Type}.
    Context {typD : list Type -> typ -> Type}.
    Context {func : Type}.
    Variable RType_typ : RType typD.
    Variable TI_Fun : TypInstance2 typD Fun.
    Variable RSym_func : RSym typD func.
    Variable us : env typD.


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
    Definition exprD e us vs t
    : option (typD nil t) :=
      let (tus,gus) := split_env us in
      let (tvs,gvs) := split_env vs in
      match @exprD' typ typD func _ _ _ e tus tvs t with
        | None => None
        | Some f => Some (f gus gvs)
      end.

    Axiom exprD_Var : forall ve v t,
      exprD (Var v) us ve t = lookupAs ve v t.

    Axiom exprD_UVar : forall ve u t,
      exprD (UVar u) us ve t = lookupAs us u t.

    Axiom exprD_Sym : forall ve f t,
      exprD (Inj f) us ve t = symAs f t.

    Let tyArr_outof : forall ts l r, typD ts (typ2 l r) -> typD ts l -> typD ts r :=
      fun ts l r => @Iso.soutof _ _ (typ2_iso ts l r) (fun x => x).
    Let tyArr_into : forall ts l r, (typD ts l -> typD ts r) -> typD ts (typ2 l r) :=
      fun ts l r => @Iso.sinto _ _ (typ2_iso ts l r) (fun x => x).

(*
    Axiom exprD_Abs_is_arr : forall vs e t t',
      exprD (Abs t' e) us vs t =
      @typ2_matchW _ _ _ TI_Fun nil t
                  (fun t'' _ => option (typD nil t''))
                  (fun l r =>
                     bind (Monad := Monad_option) (type_cast nil t' l)
                          (fun cast =>
                             let cast := cast (fun x => x -> typD nil r) in
                             bind (exprD (Abs t' e) us vs (typ2 t' r))
                                  (fun x =>
                                     Some (tyArr_into (cast (tyArr_outof _ x))))))
                  (fun _ => None).
*)

    Axiom typeof_expr_eq_exprD_False : forall l ve e t,
      WellTyped_expr (typeof_env us) (l :: typeof_env ve) e t ->
      forall x, exprD e us (existT _ l x :: ve) t = None ->
                False.

    Axiom typeof_expr_exprD' : forall us vs e t,
      WellTyped_expr us vs e t <->
      exists v, exprD' e us vs t = Some v.

    Axiom exprD_App : forall ve t e arg,
      exprD (App e arg) us ve t =
      @typ2_matchW _ _ _ TI_Fun nil t
                  (fun T => option T -> option (typD nil t))
                  (fun l r => fun f' =>
                     match f'
                         , exprD arg us ve l
                         , type_cast nil r t
                     with
                       | Some f , Some x , Some cast =>
                         Some (cast (fun x => x) (f x))
                       | _ , _ , _ => None
                     end)
                  (fun _ => fun _ => None)
                  (exprD e us ve t).
  End with_types.

End ExprDenote.
*)

(**
Module Build_ExprDenote (EDc : ExprDenote_core) <:
       ExprDenote with Definition exprD' := @EDc.exprD'.
  Require Import ExtLib.Tactics.Consider.
  Require Import ExtLib.Tactics.Injection.
  Require Import ExtLib.Data.ListNth.

  Include EDc.

  Section with_types.
    Context {typ : Type}.
    Context {typD : list Type -> typ -> Type}.
    Context {func : Type}.
    Context {RType_typ : RType typD}.
    Context {RTypeOk_typ : RTypeOk RType_typ}.
    Context {TI_Fun : TypInstance2 typD Fun}.
    Context {TIOK_Fun : TypInstance2_Ok TI_Fun}.
    Context {RSym_func : RSym typD func}.
    Variable us : env typD.

    Definition exprD us vs e t
    : option (typD nil t) :=
      let (tvs,gvs) := split_env vs in
      match @exprD' _ _ _ _ _ us tvs e t with
        | None => None
        | Some f => Some (f gvs)
      end.

    Ltac think :=
      repeat match goal with
               | |- context [ type_cast ?A ?B ?C ?C ] =>
                 let H := fresh in
                 destruct (type_cast_refl B C A) as [ ? [ H ? ] ] ;
                 rewrite H
             end.

    Theorem typeof_expr_exprD'_impl : forall vs e t,
      typeof_expr (typeof_env us) vs e = Some t ->
      exists val, exprD' us vs e t = Some val.
    Proof.
      intros vs e; revert vs.
      induction e; simpl; intros.
      { rewrite exprD'_Var.
        match goal with
          | |- context [ @eq_refl ?A ?B ] =>
            generalize (@eq_refl A B)
        end.
        revert H.
        generalize (nth_error vs v) at 1 2 4.
        intros. subst.
        think. eauto. }
      { rewrite exprD'_Sym.
        unfold symAs.
        generalize (symD f). rewrite H. intros.
        think. eauto. }
      { rewrite (@exprD'_App _ _ _ RType_typ TI_Fun RSym_func).
        specialize (IHe1 vs). specialize (IHe2 vs).
        forward.
        simpl.
        destruct (IHe1 _ eq_refl); clear IHe1.
        destruct (IHe2 _ eq_refl); clear IHe2.
        unfold type_of_apply in *.
        destruct (@typ2_matchW_case _ _ _ TI_Fun _ nil t0).
        { destruct H4. destruct H4. destruct H4. destruct H4.
          rewrite H5 in *.
          Require Import MirrorCore.IsoTac.
          iso_norm.
          forward. inv_all. subst.
          exists (fun g : hlist (typD nil) vs =>
                    ((@Iso.sinto _ _ x3 (fun x => x) (x g)) (p (x0 g)))).
          rewrite H2.
          erewrite IsoTac.soutof_app''; eauto with typeclass_instances.
          erewrite sinto_option by  eauto with typeclass_instances.
          destruct (type_cast_refl nil t (fun x => x)). destruct H6.
          match goal with
            | H : ?Y = Some _ |- context [ ?X ] =>
              change X with Y; rewrite H
          end.
          (** TODO: this proof can not work. The problem comes from
           ** the structure of the denotation.
           ** - In exprD, I use the type inferred from the function to
           **   evaluate the argument.
           ** - In typeof_expr, I determine both types and check that
           **   they are compatible.
           ** This is equivalent if type_cast checks definitional equality
           ** otherwise, we would need a lemma that would say something
           ** about consistent casts. We would use this to prove that equivalent
           ** types have consistent denotations through the isomorphism.
           ** This property has to talk about everything and is therefore
           ** very hairy...
           **
           ** It should be noted that this isn't a complete deal-breaker, but
           ** it does force us to us bi-directional typing in both typeof_expr
           ** and exprD (or not use it in either).
           **)
          {
        destruct t0; simpl in *; try congruence.
        change typ_eqb with (@rel_dec _ (@eq typ) _) in *.
        consider (t0_1 ?[ eq ] t1); intros; subst; try congruence.
        rewrite H0.
        destruct (IHe2 _ eq_refl). rewrite H.
        inv_all; subst. rewrite type_cast_typ_refl.
        eauto. }
      { rewrite exprD'_Abs.
        specialize (IHe (t :: vs)).
        destruct (typeof_expr (typeof_env us) (t :: vs) e); try congruence.
        inv_all; subst.
        specialize (IHe _ eq_refl).
        destruct IHe.
        rewrite type_cast_typ_refl. rewrite H. eauto. }
      { rewrite exprD'_UVar.
        unfold lookupAs.
        rewrite nth_error_typeof_env in *.
        destruct (nth_error us u); try congruence.
        inv_all; subst. destruct s; simpl.
        rewrite type_cast_typ_refl. eauto. }
    Qed.

    Theorem exprD_Var : forall ve u t,
      exprD us ve (Var u) t = lookupAs ve u t.
    Proof.
      unfold exprD; intros.
      consider (split_env ve); intros.
      unfold lookupAs.
      consider (nth_error ve u); intros.
      { eapply split_env_nth_error in H0.
        rewrite exprD'_Var.
        rewrite H in *. simpl in *.
        destruct s.
        match goal with
          | |- context [ @eq_refl ?X ?Y ] =>
            generalize (@eq_refl X Y)
        end.
        revert H0.
        change (
            let zzz e := hlist_nth e u in
            match
              nth_error x u as t1
              return
              (match t1 with
                 | Some v => typD ts nil v
                 | None => unit
               end -> Prop)
            with
              | Some v =>
                fun res : typD ts nil v =>
                  existT (typD ts nil) x0 t0 = existT (typD ts nil) v res
              | None => fun _ : unit => False
            end (zzz h) ->
            forall e : nth_error x u = nth_error x u,
              match
                match
                  nth_error x u as z
                  return
                  (z = nth_error x u ->
                   option (hlist (typD ts nil) x -> typD ts nil t))
                with
                  | Some z =>
                    fun pf : Some z = nth_error x u =>
                      match type_cast_typ ts (fun x1 : Type => x1) nil z t with
                        | Some cast =>
                          Some
                            (fun e0 : hlist (typD ts nil) x =>
                               match
                                 pf in (_ = t'')
                                 return
                                 (match t'' with
                                    | Some t1 => typD ts nil t1
                                    | None => unit
                                  end -> typD ts nil t)
                               with
                                 | eq_refl => fun x1 : typD ts nil z => cast x1
                               end (zzz e0))
                        | None => None
                      end
                  | None => fun _ : None = nth_error x u => None
                end e
              with
                | Some f => Some (f h)
                | None => None
              end =
              match type_cast_typ ts (fun x1 : Type => x1) nil x0 t with
                | Some f => Some (f t0)
                | None => None
              end).
        intro. clearbody zzz. revert zzz.
        destruct (nth_error x u); intuition.
        inv_all. destruct H0. subst.
        destruct (type_cast_typ ts (fun x1 : Type => x1) nil x0 t); auto.
        f_equal. clear.
        uip_all. reflexivity. }
      { rewrite exprD'_Var.
        match goal with
          | |- context [ @eq_refl ?X ?Y ] =>
            generalize (@eq_refl X Y)
        end.
        match goal with
          | H : ?X = ?Y |- _ =>
            assert (projT1 X = projT1 Y) by (f_equal; auto)
        end.
        change (
            let zzz e := hlist_nth e u in
            forall e : nth_error x u = nth_error x u,
              match
                match
                  nth_error x u as z
                  return
                  (z = nth_error x u ->
                   option (hlist (typD ts nil) x -> typD ts nil t))
                with
                  | Some z =>
                    fun pf : Some z = nth_error x u =>
                      match type_cast_typ ts (fun x0 : Type => x0) nil z t with
                        | Some cast =>
                          Some
                            (fun e0 : hlist (typD ts nil) x =>
                               match
                                 pf in (_ = t'')
                                 return
                                 (match t'' with
                                    | Some t0 => typD ts nil t0
                                    | None => unit
                                  end -> typD ts nil t)
                               with
                                 | eq_refl => fun x0 : typD ts nil z => cast x0
                               end (zzz e0))
                        | None => None
                      end
                  | None => fun _ : None = nth_error x u => None
                end e
              with
                | Some f => Some (f h)
                | None => None
              end = None).
        intro; clearbody zzz.
        remember (nth_error x u).
        destruct e; auto.
        exfalso.
        rewrite split_env_projT1 in H1. simpl in *. subst.
        clear - Heqe H0.
        rewrite nth_error_map in Heqe. rewrite H0 in *. congruence. }
    Qed.

    Theorem exprD_UVar : forall ve u t,
      exprD us ve (UVar u) t = lookupAs us u t.
I    Proof.
      unfold exprD; intros.
      destruct (split_env ve).
      rewrite exprD'_UVar.
      unfold lookupAs.
      consider (nth_error us u); intros; auto.
      destruct s.
      destruct (TypesI.type_cast (fun x1 : Type => x1) nil x0 t); auto.
    Qed.

    Theorem exprD_Sym : forall ve f t,
      exprD us ve (Inj f) t = funcAs f t.
    Proof.
      unfold exprD. intros.
      destruct (split_env ve).
      rewrite exprD'_Sym.
      forward.
    Qed.

    Theorem exprD_App : forall ve t e arg,
      exprD us ve (App e arg) t =
      match typeof_expr (typeof_env us) (typeof_env ve) e with
        | Some (tvArr l r) =>
          match exprD us ve e (tvArr l r)
              , exprD us ve arg l
              , type_cast_typ _ (fun x => x) _ r t
          with
            | Some f , Some x , Some cast =>
              Some (cast (f x))
            | _ , _ , _ => None
          end
        | _ => None
      end.
    Proof.
      unfold exprD; intros.
      unfold typeof_env. rewrite <- (split_env_projT1 ve).
      destruct (split_env ve).
      rewrite exprD'_App.
      simpl in *. unfold typeof_env.
      destruct (typeof_expr (map (projT1 (P:=typD ts nil)) us) x e); auto.
      destruct t0; auto.
      repeat match goal with
               | |- match match ?X with _ => _ end with _ => _ end =
                    match match ?Y with _ => _ end with _ => _ end =>
                 change X with Y; destruct Y; auto
             end.
      destruct (type_cast_typ ts (fun x0 : Type => x0) nil t0_2 t); auto.
    Qed.

    Theorem exprD_Abs_is_arr : forall vs e t t',
      exprD us vs (Abs t' e) t =
      match t as t return option (typD ts nil t) with
        | tvArr l r =>
          if t' ?[ eq ] l then
            exprD us vs (Abs l e) (tvArr l r)
          else None
        | _ => None
      end.
    Proof.
      unfold exprD. intros; destruct (split_env vs).
      rewrite exprD'_Abs.
      destruct t; auto.
      rewrite exprD'_Abs.
      consider (t' ?[ eq ] t1); intros; subst; try reflexivity.
      match goal with
        | |- match match ?x with _ => _ end with _ => _ end = _ =>
          consider x; intros; auto
      end.
      generalize (@type_cast_typ_eq _ _ _ _ _ _ H0).
      congruence.
    Qed.

    Theorem typeof_expr_eq_exprD_False : forall l ve e t,
      WellTyped_expr (typeof_env us) (l :: typeof_env ve) e t ->
      forall x, exprD us (existT _ l x :: ve) e t = None ->
                False.
    Proof.
      intros. unfold exprD in *. simpl in *.
      unfold WellTyped_expr in *.
      eapply typeof_expr_exprD'_impl in H. destruct H.
      revert H0 H.
      generalize (projT2 (split_env ve)).
      rewrite split_env_projT1.
      intros.
      match goal with
        | H : ?Y = _ , H' : match ?X with _ => _ end = _ |- _ =>
          change X with Y in * ; rewrite H in H'
      end. congruence.
    Qed.

    Lemma lem_typeof_expr_exprD' : forall vs e t,
      WellTyped_expr (typeof_env us) vs e t <->
      exprD' us vs e t <> None.
    Proof.
      intros vs e. revert vs. induction e; simpl; intros.
      { rewrite WellTyped_expr_Var.
        rewrite exprD'_Var.
        split; intros.
        { gen_refl.
          change (
              let zzz z (pf : Some z = nth_error vs v) cast :=
                  (fun e0 : hlist (typD ts nil) vs =>
                               match
                                 pf in (_ = t'')
                                 return
                                 (match t'' with
                                    | Some t0 => typD ts nil t0
                                    | None => unit
                                  end -> typD ts nil t)
                               with
                                 | eq_refl => fun x : typD ts nil z => cast x
                               end (hlist_nth e0 v))
              in
              forall e : nth_error vs v = nth_error vs v,
                match
                  nth_error vs v as z
                  return
                  (z = nth_error vs v ->
                   option (hlist (typD ts nil) vs -> typD ts nil t))
                with
                  | Some z =>
                    fun pf : Some z = nth_error vs v =>
                      match type_cast_typ ts (fun x : Type => x) nil z t with
                        | Some cast =>
                          Some (zzz z pf cast)
                        | None => None
                      end
                  | None => fun _ : None = nth_error vs v => None
                end e <> None
            ).
          intro zzz; clearbody zzz.
          destruct (nth_error vs v); try congruence.
          inv_all; subst. intros.
          rewrite type_cast_typ_refl. congruence. }
        { revert H.
          gen_refl.
          change (
              let zzz z (pf : Some z = nth_error vs v) cast :=
                  (fun e0 : hlist (typD ts nil) vs =>
                               match
                                 pf in (_ = t'')
                                 return
                                 (match t'' with
                                    | Some t0 => typD ts nil t0
                                    | None => unit
                                  end -> typD ts nil t)
                               with
                                 | eq_refl => fun x : typD ts nil z => cast x
                               end (hlist_nth e0 v)) in
              forall e : nth_error vs v = nth_error vs v,
                match
                  nth_error vs v as z
                  return
                  (z = nth_error vs v ->
                   option (hlist (typD ts nil) vs -> typD ts nil t))
                with
                  | Some z =>
                    fun pf : Some z = nth_error vs v =>
                      match type_cast_typ ts (fun x : Type => x) nil z t with
                        | Some cast =>
                          Some (zzz z pf cast)
                        | None => None
                      end
                  | None => fun _ : None = nth_error vs v => None
                end e <> None -> nth_error vs v = Some t).
          intro zzz; clearbody zzz.
          destruct (nth_error vs v); try congruence.
          intros. f_equal.
          revert H.
          match goal with
            | |- context [ match ?X with _ => _ end = _ ] =>
              consider X
          end; try congruence; intros.
          apply (type_cast_typ_eq _ _ _ _ _ H). } }
      { rewrite WellTyped_expr_Func.
        rewrite exprD'_Sym.
        unfold funcAs.
        generalize (symD f).
        destruct (typeof_sym f); intuition; try congruence.
        { inv_all; subst. simpl in *.
          rewrite type_cast_typ_refl in *. congruence. }
        { simpl in *. forward.
          inv_all; subst.
          generalize (type_cast_typ_eq _ _ _ _ _ H); intros.
          f_equal; auto. } }
      { rewrite WellTyped_expr_App.
        rewrite exprD'_App.
        split; intros.
        { destruct H. destruct H.
          rewrite IHe1 in *. rewrite IHe2 in *.
          destruct H. destruct H0.
          consider (typeof_expr (typeof_env us) vs e1); intros.
          { generalize H. generalize H0.
            eapply IHe1 in H. eapply IHe2 in H0.
            red in H; red in H0. rewrite H in H2. inv_all; subst.
            destruct t0; simpl in *; try congruence.
            change typ_eqb with (@rel_dec _ (@eq typ) _) in *.
            consider (t0_1 ?[ eq ] x0); try congruence; intros; inv_all; subst.
            destruct (exprD' us vs e1 (tvArr x0 t)); intuition.
            destruct (exprD' us vs e2 x0); intuition.
            rewrite type_cast_typ_refl in H1; congruence. }
          { exfalso.
            eapply IHe1 in H. red in H. congruence. } }
        { consider (typeof_expr (typeof_env us) vs e1);
          try congruence; intros.
          destruct t0; try congruence.
          repeat match goal with
                   | _ : not (match ?X with _ => _ end = _) |- _ =>
                     consider X; intros
                 end; try congruence.
          generalize (type_cast_typ_eq _ _ _ _ _ H2); intros.
          consider (exprD' us vs e1 (tvArr t0_1 t0_2)); intros; try congruence.
          inv_all. rewrite H5 in *.
          exists (tvArr t0_1 t0_2). exists t0_1.
          simpl.
          change typ_eqb with (@rel_dec _ (@eq typ) _) in *.
          consider (t0_1 ?[ eq ] t0_1); try congruence; intros.
          rewrite IHe1. rewrite IHe2.
          rewrite H4 in *. eapply typeof_expr_exprD'_impl in H.
          destruct H. rewrite H. rewrite H1. intuition congruence. } }
      { rewrite WellTyped_expr_Abs.
        rewrite exprD'_Abs.
        { split; intros.
          { destruct H. destruct H; subst.
            rewrite type_cast_typ_refl.
            consider (exprD'  us (t :: vs) e x); try congruence.
            intros. intro. eapply IHe; eauto. }
          { destruct t0; intuition try congruence.
            repeat match goal with
                     | _ : match ?x with _ => _ end = _ -> False |- _ =>
                       consider x; intuition
                   end.
            generalize (type_cast_typ_eq _ _ _ _ _ H); intro; subst.
            exists t0_2. intuition.
            eapply IHe. rewrite H0. congruence. } } }
      { rewrite WellTyped_expr_UVar.
        rewrite exprD'_UVar.
        rewrite nth_error_typeof_env.
        unfold lookupAs in *.
        destruct (nth_error us u).
        { split; intro.
          { destruct s. inv_all; subst. simpl in *.
            rewrite type_cast_typ_refl. congruence. }
          { destruct s. simpl in *.
            match goal with
              | _ : not (match ?x with _ => _ end = _) |- _ =>
                consider x; intuition
            end.
            match goal with
              | _ : match ?X with _ => _ end = _ |- _ =>
                consider X; intros; try congruence
            end.
            inv_all; subst.
            f_equal; eapply (type_cast_typ_eq _ _ _ _ _ H). } }
        { intuition congruence. } }
    Qed.

    Theorem typeof_expr_exprD' : forall vs e t,
      WellTyped_expr (typeof_env us) vs e t <->
      exists v, exprD' us vs e t = Some v.
    Proof.
      intros.
      rewrite lem_typeof_expr_exprD'.
      intuition.
      destruct (exprD' us vs e t); intuition. eauto.
      destruct H. congruence.
    Qed.

    Theorem typeof_expr_exprD : forall vs e t,
      WellTyped_expr (typeof_env us) (typeof_env vs) e t <->
      exists v, exprD us vs e t = Some v.
    Proof.
      intros. rewrite typeof_expr_exprD'.
      unfold exprD.
      consider (split_env vs); intros.
      assert (x = typeof_env vs).
      { clear - H. unfold typeof_env.
        rewrite <- split_env_projT1. rewrite H. reflexivity. }
      subst. intuition.
      { destruct H0.
        eexists.
        match goal with
          | H : ?X = _ |- match ?Y with _ => _ end = _ =>
            change Y with X ; rewrite H; auto
        end. }
      { destruct H0.
        match goal with
          | H : match ?X with _ => _ end = _ |- exists v, ?Y = _ =>
            change Y with X ; destruct X ; try congruence
        end. eauto. }
    Qed.

  End with_envs.
End Build_ExprDenote.
**)


(** This works but it isn't "nice"

    Check @bind.
    Axiom dbind : forall m : Type -> Type,
                    forall T U,
                    m T ->
                    (forall x : T, m (U x)) ->
                    m { t : T & U t }.

    Axiom dbind_cps : forall m : Type -> Type,
                      forall T U,
                        m T ->
                        (forall x : T, m (U x)) ->
                    m { t : T & U t }.
 **)
