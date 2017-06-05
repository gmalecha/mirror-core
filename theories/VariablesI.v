Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.CtxLogic.

Set Implicit Arguments.
Set Strict Implicit.

Section with_Expr.
  Variable typ : Type.
  Variable expr : Type.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Expr_expr : @Expr typ _ expr}.

  (** Variables **)
  Class ExprVar : Type :=
  { Var : var -> expr
  }.

  Class ExprVarOk (EV : ExprVar) : Prop :=
  { Var_exprD
    : forall tus tvs v t,
      match exprD tus tvs t (Var v) with
      | None =>
        nth_error tvs v = None \/
        exists t', nth_error tvs v = Some t' /\ ~Rty t t'
      | Some vD =>
        exists get,
        nth_error_get_hlist_nth typD tvs v = Some (@existT _ _ t get) /\
        forall us vs,
          get vs = vD us vs
      end
  ; mentionsV_Var : forall v v', mentionsV v (Var v') = true <-> v = v'
  }.

  Lemma exprD_exact_var {EV} {EVO : ExprVarOk EV} tus tvs tvs' t
  : exists eD' : exprT tus (tvs ++ t :: tvs') (typD t),
      exprD tus (tvs ++ t :: tvs') t (Var (length tvs)) = Some eD' /\
      (forall (us : hlist typD tus) (vs : hlist typD tvs) vs'
        (x : typD t), eD' us (hlist_app vs (Hcons x vs')) = x).
  Proof.
    generalize (Var_exprD tus (tvs ++ t :: tvs') (length tvs) t).
    destruct (exprD tus (tvs ++ t :: tvs') t (Var (length tvs))).
    { destruct 1 as [ ? [ ? ? ] ]. eexists; split; eauto.
      intros. rewrite <- H0; clear H0. clear - H RTypeOk_typ.
      eapply nth_error_get_hlist_nth_appR in H; eauto.
      simpl in H. destruct H as [ ? [ ? ? ] ].
      rewrite Minus.minus_diag in H.
      inv_all.
      rewrite H0. subst. reflexivity. }
    { intros. exfalso.
      rewrite ListNth.nth_error_app_R in H by reflexivity.
      rewrite NPeano.Nat.sub_diag in H.
      simpl in *. unfold value in *.
      destruct H; try congruence.
      destruct H. destruct H.
      inversion H. apply H0. assumption. }
  Qed.

  (** Unification Variables **)
  Class ExprUVar : Type :=
  { UVar : uvar -> expr
  }.

  Class ExprUVarOk (EU : ExprUVar) : Prop :=
  { UVar_exprD
    : forall tus tvs v t,
      match exprD tus tvs t (UVar v) with
      | None =>
        nth_error tus v = None \/
        exists t', nth_error tus v = Some t' /\ ~Rty t t'
      | Some vD =>
        exists get,
        nth_error_get_hlist_nth typD tus v = Some (@existT _ _ t get) /\
        forall us vs,
          get us = vD us vs
      end
  ; mentionsU_UVar : forall v v', mentionsU v (UVar v') = true <-> v = v'
  }.

  Lemma exprD_exact_uvar {EU} {EUO : ExprUVarOk EU} tus tus' tvs t
  : exists eD' : exprT (tus ++ t :: tus') tvs (typD t),
      exprD (tus ++ t :: tus') tvs t (UVar (length tus)) = Some eD' /\
      (forall (us : hlist typD tus) us' (vs : hlist typD tvs)
        (x : typD t), eD' (hlist_app us (Hcons x us')) vs = x).
  Proof.
    generalize (UVar_exprD (tus ++ t :: tus') tvs (length tus) t).
    destruct (exprD (tus ++ t :: tus') tvs t (UVar (length tus))).
    { destruct 1 as [ ? [ ? ? ] ]. eexists; split; eauto.
      intros. rewrite <- H0; clear H0. clear - H RTypeOk_typ.
      eapply nth_error_get_hlist_nth_appR in H; eauto.
      simpl in H. destruct H as [ ? [ ? ? ] ].
      rewrite Minus.minus_diag in H.
      inv_all.
      rewrite H0. subst. reflexivity. }
    { intros. exfalso.
      rewrite ListNth.nth_error_app_R in H by reflexivity.
      rewrite Minus.minus_diag in H.
      simpl in *. unfold value in *.
      destruct H; try congruence.
      destruct H. destruct H.
      inversion H. apply H0. assumption. }
  Qed.

  Definition sem_preserves_if_ho tus tvs
             (P : exprT tus tvs Prop -> Prop)
             (f : uvar -> option expr) : Prop :=
    forall u e t get,
      f u = Some e ->
      nth_error_get_hlist_nth _ tus u = Some (@existT _ _ t get) ->
      exists eD,
        exprD tus tvs t e = Some eD /\
        P (fun us vs => get us = eD us vs).

  Definition sem_preserves_if tus tvs
             (P : exprT tus tvs Prop)
             (f : uvar -> option expr) : Prop :=
    @sem_preserves_if_ho tus tvs
                         (fun P' => forall us vs, P us vs -> P' us vs) f.

  Definition instantiate_spec_ho
             (instantiate : (uvar -> option expr) -> nat -> expr -> expr)
    : Prop :=
    forall tus tvs f e tvs' t eD P (EApp : CtxLogic.ExprTApplicative P),
      sem_preserves_if_ho P f ->
      exprD tus (tvs' ++ tvs) t e = Some eD ->
      exists eD',
        exprD tus (tvs' ++ tvs) t (instantiate f (length tvs') e) = Some eD' /\
        P (fun us vs => forall vs',
               eD us (hlist_app vs' vs) = eD' us (hlist_app vs' vs)).

  (** Converting Variables to Unification Variables **)
  Definition vars_to_uvars_spec
             (vars_to_uvars : nat -> nat -> expr -> expr)
  : Prop :=
    forall (tus : tenv typ) (e : expr) (tvs : list typ)
           (t : typ) (tvs' : list typ)
           (val : hlist typD tus ->
                  hlist typD (tvs ++ tvs') -> typD t),
      exprD tus (tvs ++ tvs') t e = Some val ->
      exists
        val' : hlist typD (tus ++ tvs') ->
               hlist typD tvs -> typD t,
        let e' := vars_to_uvars (length tvs) (length tus) e in
        exprD (tus ++ tvs') tvs t e' = Some val' /\
        (forall (us : hlist typD tus)
                (vs' : hlist typD tvs') (vs : hlist typD tvs),
           val us (hlist_app vs vs') = val' (hlist_app us vs') vs).

End with_Expr.

Arguments ExprVar expr : rename.
Arguments ExprUVar expr : rename.
Arguments ExprVarOk {typ expr _ _} _ : rename.
Arguments ExprUVarOk {typ expr _ _} _ : rename.
