Require Import Coq.Lists.List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.EnvI.

Set Implicit Arguments.
Set Strict Implicit.

Section with_Expr.
  Variable typ : Type.
  Variable expr : Type.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Expr_expr : @Expr typ _ expr}.

  Class ExprVar : Type :=
  { Var : nat -> expr
  ; mentionsV : nat -> expr -> bool
  }.

  Class ExprVarOk (EV : ExprVar) : Prop :=
  { Var_exprD'
    : forall tus tvs v t,
        match exprD' tus tvs (Var v) t with
          | None =>
            nth_error tvs v = None \/
            exists t', nth_error tvs v = Some t' /\ ~Rty t t'
          | Some vD =>
            exists get,
            nth_error_get_hlist_nth typD tvs v = Some (@existT _ _ t get) /\
            forall us vs,
              get vs = vD us vs
        end
  ; exprD'_strengthenV_single
    : forall tus tvs e t t' val,
      mentionsV (length tvs) e = false ->
      exprD' tus (tvs ++ t :: nil) e t' = Some val ->
      exists val',
        exprD' tus tvs e t' = Some val' /\
        forall us vs u,
          val us (hlist_app vs (Hcons u Hnil)) = val' us vs
  ; mentionsV_Var : forall v v', mentionsV v (Var v') = true <-> v = v'
  }.

  Lemma exprD'_exact_var {EV} {EVO : ExprVarOk EV} tus tvs tvs' t
  : exists eD' : exprT tus (tvs ++ t :: tvs') (typD t),
      exprD' tus (tvs ++ t :: tvs') (Var (length tvs)) t = Some eD' /\
      (forall (us : hlist typD tus) (vs : hlist typD tvs) vs'
        (x : typD t), eD' us (hlist_app vs (Hcons x vs')) = x).
  Proof.
    generalize (Var_exprD' tus (tvs ++ t :: tvs') (length tvs) t).
    destruct (exprD' tus (tvs ++ t :: tvs') (Var (length tvs)) t).
    { destruct 1 as [ ? [ ? ? ] ]. eexists; split; eauto.
      intros. rewrite <- H0; clear H0. clear - H RTypeOk_typ.
      eapply nth_error_get_hlist_nth_appR in H; eauto.
      simpl in H. destruct H as [ ? [ ? ? ] ].
      rewrite Minus.minus_diag in H.
      inv_all.
      rewrite H0. subst. reflexivity. }
    { intros. exfalso.
      rewrite ListNth.nth_error_app_R in H by omega.
      cutrewrite (length tvs - length tvs = 0) in H; [ | omega ].
      simpl in *. unfold value in *.
      destruct H; try congruence.
      destruct H. destruct H.
      inversion H. apply H0. assumption. }
  Qed.

  Class ExprUVar : Type :=
  { UVar : nat -> expr
  ; mentionsU : nat -> expr -> bool
  }.

  Class ExprUVarOk (EU : ExprUVar) : Prop :=
  { UVar_exprD'
    : forall tus tvs v t,
        match exprD' tus tvs (UVar v) t with
          | None =>
            nth_error tus v = None \/
            exists t', nth_error tus v = Some t' /\ ~Rty t t'
          | Some vD =>
            exists get,
            nth_error_get_hlist_nth typD tus v = Some (@existT _ _ t get) /\
            forall us vs,
              get us = vD us vs
        end
  ; exprD'_strengthenU_single
    : forall tus tvs e t t' val,
      mentionsU (length tus) e = false ->
      exprD' (tus ++ t :: nil) tvs e t' = Some val ->
      exists val',
        exprD' tus tvs e t' = Some val' /\
        forall us vs u,
          val (hlist_app us (Hcons u Hnil)) vs = val' us vs
  ; mentionsU_UVar : forall v v', mentionsU v (UVar v') = true <-> v = v'
  }.

  Lemma exprD'_exact_uvar {EU} {EUO : ExprUVarOk EU} tus tus' tvs t
  : exists eD' : exprT (tus ++ t :: tus') tvs (typD t),
      exprD' (tus ++ t :: tus') tvs (UVar (length tus)) t = Some eD' /\
      (forall (us : hlist typD tus) us' (vs : hlist typD tvs)
        (x : typD t), eD' (hlist_app us (Hcons x us')) vs = x).
  Proof.
    generalize (UVar_exprD' (tus ++ t :: tus') tvs (length tus) t).
    destruct (exprD' (tus ++ t :: tus') tvs (UVar (length tus)) t).
    { destruct 1 as [ ? [ ? ? ] ]. eexists; split; eauto.
      intros. rewrite <- H0; clear H0. clear - H RTypeOk_typ.
      eapply nth_error_get_hlist_nth_appR in H; eauto.
      simpl in H. destruct H as [ ? [ ? ? ] ].
      rewrite Minus.minus_diag in H.
      inv_all.
      rewrite H0. subst. reflexivity. }
    { intros. exfalso.
      rewrite ListNth.nth_error_app_R in H by omega.
      rewrite Minus.minus_diag in H.
      simpl in *. unfold value in *.
      destruct H; try congruence.
      destruct H. destruct H.
      inversion H. apply H0. assumption. }
  Qed.

End with_Expr.

Arguments ExprVar expr : rename.
Arguments ExprUVar expr : rename.
Arguments ExprVarOk {typ _ expr _} _ : rename.
Arguments ExprUVarOk {typ _ expr _} _ : rename.
