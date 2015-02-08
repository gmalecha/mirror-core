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
  Context {ExprOk_expr : ExprOk Expr_expr}.

  Class ExprSubstI : Type :=
  { expr_subst
    : (uvar -> option expr) -> (var -> option expr) -> nat -> expr -> expr
  }.

  Variable subst : ExprSubstI.

  Record ExprTApplicativeR (tus tvs tus' tvs' : tenv typ)
         (C : exprT tus tvs (exprT tus' tvs' Prop) -> Prop)
  : Type :=
  { exprTPureR : forall (P : exprT tus tvs (exprT tus' tvs' Prop)),
      (forall a b c d, P a b c d) -> C P
  ; exprTApR : forall P Q : exprT tus tvs (exprT tus' tvs' Prop),
        C (fun a b c d => P a b c d -> Q a b c d) -> C P -> C Q
  }.

  Class ExprSubstOk : Prop :=
  { expr_subst_sound_ho
    : forall substU substV n e e',
        expr_subst substU substV n e = e' ->
        forall _tvs tus tvs tus' tvs'
               (P : exprT tus tvs (exprT tus' tvs' Prop) -> Prop)
               (ExprTApR : ExprTApplicativeR P)
          (H_substU : forall u t get,
              nth_error_get_hlist_nth typD tus u = Some (@existT _ _ t get) ->
              match substU u with
                | Some eU =>
                  exists eUD,
                  exprD' tus' tvs' eU t = Some eUD /\
                  P (fun us vs us' vs' => get us = eUD us' vs')
                | None => exists get',
                  nth_error_get_hlist_nth typD tus' u = Some (@existT _ _ t get')
                  /\ P (fun us vs us' vs' => get us = get' us')
              end)
          (H_substV : forall u t get,
              nth_error_get_hlist_nth typD tvs u = Some (@existT _ _ t get) ->
              match substV u with
                | Some eV =>
                  exists eVD,
                  exprD' tus' tvs' eV t = Some eVD /\
                  P (fun us vs us' vs' => get vs = eVD us' vs')
                | None => exists get',
                  nth_error_get_hlist_nth typD tvs' u = Some (@existT _ _ t get')
                  /\ P (fun us vs us' vs' => get vs = get' vs')
              end),
          forall t eD,
            length _tvs = n ->
            exprD' tus (_tvs ++ tvs) e t = Some eD ->
            exists eD',
              exprD' tus' (_tvs ++ tvs') e' t = Some eD' /\
              P (fun us vs us' vs' => forall _vs,
                     eD us (HList.hlist_app _vs vs) = eD' us' (HList.hlist_app _vs vs'))
  ; mentionsU_subst :
      forall substU substV n u e,
        mentionsU u (expr_subst substU substV n e) = true <->
        (   (mentionsU u e = true /\ substU u = None)
         \/ (exists u' e', mentionsU u' e = true /\
                           substU u' = Some e' /\
                           mentionsU u e' = true)
         \/ (exists v' e', mentionsV (n+v') e = true /\
                           substV v' = Some e' /\
                           mentionsU u e' = true))
  ; mentionsV_subst :
      forall substU substV n v e,
        mentionsV v (expr_subst substU substV n e) = true <->
        (   (v < n /\ mentionsV v e = true)
         \/ (v > n /\
             (   (mentionsV v e = true /\ substV v = None)
              \/ (exists u' e', mentionsU u' e = true /\
                                substU u' = Some e' /\
                                mentionsV v e' = true)
              \/ (exists v' e', mentionsV (n+v') e = true /\
                                substV v' = Some e' /\
                                mentionsV v e' = true))))
  ; Proper_subst : Proper ((eq ==> eq) ==> (eq ==> eq) ==> eq ==> eq ==> eq) expr_subst
  }.

  Definition instantiate (f : uvar -> option expr) (n : nat) (e : expr) : expr :=
    expr_subst f (fun _ => None) n e.

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

  Definition instantiate_spec
             (instantiate : (uvar -> option expr) -> nat -> expr -> expr)
  : Prop :=
    forall tus tvs f e tvs' t eD P,
      @sem_preserves_if tus tvs P f ->
      exprD' tus (tvs' ++ tvs) e t = Some eD ->
      exists eD',
        exprD' tus (tvs' ++ tvs) (instantiate f (length tvs') e) t = Some eD' /\
        forall us vs vs',
          P us vs ->
          eD us (hlist_app vs' vs) = eD' us (hlist_app vs' vs).

  Context {ESO : ExprSubstOk}.

  Theorem instantiate_sound_ho
  : instantiate_spec_ho instantiate.
  Proof.
    red. unfold instantiate.
    intros. remember (expr_subst f (fun _ : var => None) (length tvs') e).
    symmetry in Heqe0.
    eapply expr_subst_sound_ho
      with (tus:=tus) (tvs:=tvs) (tus':=tus) (tvs':=tvs) (_tvs:=tvs') (t:=t)
           (P:=fun Q => P (fun a b => Q a b a b)) (eD := eD) in Heqe0;
      eauto.
    { clear - EApp.
      constructor.
      { intros. eapply exprTPure. eauto. }
      { intros. revert H0. eapply exprTAp. eauto. } }
    { clear Heqe0 H0. intros.
      specialize (H u).
      destruct (f u).
      { specialize (H _ _ _ eq_refl H0).
        forward_reason.
        eexists; split; eauto. }
      { eexists; split; eauto.
        eapply exprTPure; eauto. } }
    { intros; eexists; split; eauto.
      eapply exprTPure; eauto. }
  Qed.

  Theorem instantiate_sound
  : instantiate_spec instantiate.
  Proof.
    red. intros.
    eapply instantiate_sound_ho in H0; eauto.
    { forward_reason.
      eexists; split; eauto. }
    { eapply ExprTApplicative_foralls_impl. }
  Qed.

End with_Expr.

Arguments ExprSubstI expr : rename.
Arguments ExprSubstOk typ expr RType Expr ExprSubst : rename.
