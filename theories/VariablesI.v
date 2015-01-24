Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Tactics.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.EnvI.
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



  (** Unification Variables **)
  Class ExprUVar : Type :=
  { UVar : uvar -> expr
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

  Definition sem_preserves_if_ho tus tvs
             (P : exprT tus tvs Prop -> Prop)
             (f : uvar -> option expr) : Prop :=
    forall u e t get,
      f u = Some e ->
      nth_error_get_hlist_nth _ tus u = Some (@existT _ _ t get) ->
      exists eD,
        exprD' tus tvs e t = Some eD /\
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
      exprD' tus (tvs' ++ tvs) e t = Some eD ->
      exists eD',
        exprD' tus (tvs' ++ tvs) (instantiate f (length tvs') e) t = Some eD' /\
        P (fun us vs => forall vs',
               eD us (hlist_app vs' vs) = eD' us (hlist_app vs' vs)).


(**
  (** Mentions Any **)
  Class MentionsAny : Type :=
  { mentionsAny : (uvar -> bool) -> (var -> bool) -> expr -> bool }.

  Class MentionsAnyOk (MA : MentionsAny)
  : Type :=
  { Proper_mentionsAny
    : Proper ((eq ==> eq) ==> (eq ==> eq) ==> eq ==> eq) mentionsAny
  ; mentionsAny_weaken
    : forall pu pu' pv pv',
        (forall u, pu u = false -> pu' u = false) ->
        (forall v, pv v = false -> pv' v = false) ->
        forall e, mentionsAny pu pv e = false ->
                  mentionsAny pu' pv' e = false
  ; mentionsAny_factor
    : forall fu fu' fv fv' e,
          mentionsAny (fun u => fu u || fu' u) (fun v => fv v || fv' v) e
        = mentionsAny fu fv e || mentionsAny fu' fv' e
  ; mentionsAny_complete
    : forall pu pv e,
        mentionsAny pu pv e = true <->
        (exists u, mentionsU u e = true /\ pu u = true) \/
        (exists v, mentionsV v e = true /\ pv v = true)
  ; mentionsAny_mentionsU
    : forall u e,
        mentionsU u e = mentionsAny (fun u' => u ?[ eq ] u') (fun _ => false) e
  ; mentionsAny_mentionsV
    : forall u e,
        mentionsV u e = mentionsAny (fun _ => false) (fun u' => u ?[ eq ] u') e
  }.

  Corollary mentionsAny_complete_false
            {MA : MentionsAny} {MAO : MentionsAnyOk MA}
  : forall pu pv e,
      mentionsAny pu pv e = false <->
      (forall u, mentionsU u e = true -> pu u = false) /\
      (forall v, mentionsV v e = true -> pv v = false).
  Proof.
    intros.
    consider (mentionsAny pu pv e); intros; split; auto; intros; try congruence.
    * eapply mentionsAny_complete in H. destruct H.
      forward_reason. eauto.
      forward_reason. eauto.
    * destruct (mentionsAny_complete pu pv e).
      clear H1.
      split; intros.
      + consider (pu u); auto; intros.
        exfalso.
        rewrite H2 in H; try congruence; eauto.
      + consider (pv v); auto; intros.
        exfalso.
        rewrite H2 in H; try congruence; eauto.
  Qed.
*)

  (** Converting Variables to Unification Variables **)
  Definition vars_to_uvars_spec
             (vars_to_uvars : nat -> nat -> expr -> expr)
  : Prop :=
    forall (tus : tenv typ) (e : expr) (tvs : list typ)
           (t : typ) (tvs' : list typ)
           (val : hlist typD tus ->
                  hlist typD (tvs ++ tvs') -> typD t),
      exprD' tus (tvs ++ tvs') e t = Some val ->
      exists
        val' : hlist typD (tus ++ tvs') ->
               hlist typD tvs -> typD t,
        exprD' (tus ++ tvs') tvs (vars_to_uvars (length tvs) (length tus) e)
               t = Some val' /\
        (forall (us : hlist typD tus)
                (vs' : hlist typD tvs') (vs : hlist typD tvs),
           val us (hlist_app vs vs') = val' (hlist_app us vs') vs).

End with_Expr.

Arguments ExprVar expr : rename.
Arguments ExprUVar expr : rename.
Arguments ExprVarOk {typ _ expr _} _ : rename.
Arguments ExprUVarOk {typ _ expr _} _ : rename.
