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

    (** Reasoning principles **)
    Axiom type_cast_refl : forall x, type_cast x x = Some eq_refl.
    Axiom type_cast_total : forall x y, type_cast x y = None <-> ~Rty x y.

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

    Axiom arr_match_typ_arr
    : forall a b T tr fa,
        arr_match T (typ_arr a b) tr fa =
        match eq_sym (typD_arr a b) in _ = t return T t with
          | eq_refl => tr a b
        end.

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

    Global Instance RelDec_Correct_Rty_eq : @RelDec_Correct _ (@eq typ) _ :=
      RelDec_Correct_Rty.

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

    Lemma exprD'_deterministic
    : forall tus e tvs t1 t2 val val',
        exprD' tus tvs t1 e = Some val ->
        exprD' tus tvs t2 e = Some val' ->
        Rty t1 t2.
    Proof.
      induction e; simpl; intros; red.
      { unfold Open_GetVAs in *. simpl in *.
        forward; inv_all; subst. }
      { forward; inv_all; subst.
        unfold funcAs in *.
        generalize dependent (funcD f).
        destruct (typeof_func f); intros; try congruence.
        forward. }
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
      {  unfold Open_GetUAs in *. simpl in *.
        forward; inv_all; subst. }
    Qed.

    Local Instance EqDec_typ : EqDec typ eq.
    eauto with typeclass_instances.
    Defined.

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

    Lemma exprD'_typeof_expr
    : forall tus e tvs t val,
        exprD' tus tvs t e = Some val \/
        exprD'_simul tus tvs e = Some (@existT _ _ t val) ->
        typeof_expr tus tvs e = Some t.
    Proof.
      induction e; simpl; intros.
      { unfold Open_GetVAs, Open_UseV in *. simpl in *.
        destruct H; forward; inv_all; subst;
        eapply nth_error_get_hlist_nth_Some in H0; destruct H0; auto.
        red in r. subst. auto. }
      { unfold func_simul, funcAs in *.
        generalize dependent (funcD f).
        destruct (typeof_func f).
        { destruct 1. forward. inv_all. subst; auto. }
        { destruct 2; congruence. } }
      { destruct H; forward; inv_all; subst.
        { specialize (IHe1 _ _ _ (or_introl H1)).
          specialize (IHe2 _ _ _ (or_intror H0)).
          Cases.rewrite_all_goal.
          unfold type_of_apply.
          rewrite arr_match_typ_arr.
          rewrite type_cast_refl.
          rewrite eq_Const. reflexivity. }
        { destruct (arr_match_case x).
          { destruct H as [ ? [ ? [ ? ? ] ] ].
            rewrite H in *.
            specialize (IHe1 _ _ _ (or_intror H0)).
            repeat rewrite eq_CoFunctor in *.
            repeat rewrite eq_Const in *.
            forward.
            specialize (IHe2 _ _ _ (or_introl H1)).
            rewrite IHe2. red in x2. subst. inv_all. subst.
            unfold type_of_apply. rewrite H.
            rewrite type_cast_refl. simpl.
            rewrite eq_Const. reflexivity. }
          { rewrite H in *. congruence. } } }
      { destruct H.
        { eapply arr_match_test_None in H.
          destruct H as [ ? [ ? [ ? ? ] ] ].
          red in x1. subst. simpl in *.
          consider (exprD' tus (t :: tvs) x0 e); intros.
          { specialize (IHe _ _ _ (or_introl H)).
            rewrite IHe.
            consider (type_cast x t); intros.
            { red in r. subst; auto. }
            { exfalso. clear - H1.
              destruct (eq_sym (typD_arr x x0)).
              congruence. } }
          { exfalso. clear - H0. destruct (eq_sym (typD_arr x x0)).
            destruct (type_cast x t); congruence. } }
        { forward.
          specialize (IHe _ _ _ (or_intror H0)).
          rewrite IHe. inv_all; subst. auto. } }
      { unfold Open_GetUAs, Open_UseU in *. simpl in *.
        destruct H; forward; inv_all; subst;
        eapply nth_error_get_hlist_nth_Some in H0; destruct H0; auto.
        red in r. subst. auto. }
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
                rewrite type_cast_refl.
                split.
                { reflexivity. }
                { f_equal.
                  repeat rewrite eq_CoFunctor in *.
                  repeat rewrite eq_Const in *.
                  rewrite H6 in H1.
                  inversion H7; clear H7; subst.
                  inversion H1; clear H1; subst.
                  clear - H8. inv_all.
                  subst. reflexivity. } }
              { intros. exfalso. clear - H7.
                destruct (eq_sym (typD_arr x0 x1)).
                congruence. } }
            { exfalso.
              rewrite eq_CoFunctor in *.
              rewrite eq_Const in *.
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
