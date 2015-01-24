Require Import Coq.Bool.Bool.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Tactics.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Eq.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.OpenT.

Set Implicit Arguments.
Set Strict Implicit.

Definition var := nat.
Definition uvar := nat.

Section Expr.
  Variable typ : Type.
  Variable RType_typ : RType typ.

  Variable expr : Type.

  Definition exprT (us : tenv typ) (vs : tenv typ) (T : Type) : Type :=
    OpenT typD us (OpenT typD vs  T).

  Definition Applicative_exprT tus tvs : Applicative (exprT tus tvs) :=
    Eval cbv beta iota zeta delta [ ap pure Applicative_OpenT ] in
  {| pure := fun _ x => pure (pure x)
   ; ap := fun _ _ f x => ap (T:=OpenT typD tus)
          (ap (T:=OpenT typD tus) (pure (ap (T:=OpenT typD tvs))) f) x
   |}.
  Existing Instance Applicative_exprT.

  Definition Functor_exprT tus tvs : Functor (exprT tus tvs) :=
    Eval cbv beta iota zeta delta [ fmap Functor_OpenT ] in
  {| fmap := fun _ _ f x => fmap (fmap f) x
  |}.
  Existing Instance Functor_exprT.

  Definition RexprT (tus tvs : tenv typ) {T} (R : relation T)
  : relation (exprT tus tvs T) :=
    OpenTeq (OpenTeq R).
  Arguments RexprT _ _ {_} _ _ _.

  Global Instance Reflexive_RexprT tus tvs T (R : relation T) (_ : Reflexive R)
  : Reflexive (RexprT tus tvs R).
  Proof.
    red. eapply Reflexive_OpenTeq. eapply Reflexive_OpenTeq. assumption.
  Qed.

  Global Instance Symmetric_RexprT tus tvs T (R : relation T) (_ : Symmetric R)
  : Symmetric (RexprT tus tvs R).
  Proof.
    red. eapply Symmetric_OpenTeq. eapply Symmetric_OpenTeq. assumption.
  Qed.

  Global Instance Transitive_RexprT tus tvs T (R : relation T) (_ : Transitive R)
  : Transitive (RexprT tus tvs R).
  Proof.
    red. eapply Transitive_OpenTeq. eapply Transitive_OpenTeq. assumption.
  Qed.


  Theorem eq_exprT_eq_F tus tvs
  : forall (T : Type) (F : T -> Type) (a b : T) (pf : a = b)
         (val : exprT tus tvs (F a)),
       match pf in (_ = x) return exprT tus tvs (F x) with
       | eq_refl => val
       end =
       fun a b =>
         match pf in (_ = x) return F x with
           | eq_refl => val a b
         end.
  Proof.
    destruct pf; reflexivity.
  Qed.
  Theorem eq_exprT_eq tus tvs
  : forall (a b : Type) (pf : a = b)
         (val : exprT tus tvs a),
       match pf in (_ = x) return (exprT tus tvs x) with
       | eq_refl => val
       end =
       fun a b =>
         match pf in (_ = x) return x with
           | eq_refl => val a b
         end.
  Proof.
    destruct pf; reflexivity.
  Qed.
  Theorem eq_exprT_eq_tus tvs
  : forall T a b (pf : a = b)
         (val : exprT a tvs T),
       match pf in (_ = x) return (exprT x tvs T) with
       | eq_refl => val
       end =
       fun us =>
         val match eq_sym pf in (_ = x) return hlist _ x with
               | eq_refl => us
             end.
  Proof.
    destruct pf; reflexivity.
  Qed.
  Theorem eq_exprT_eq_tvs tvs
  : forall T a b (pf : a = b)
         (val : exprT tvs a T),
       match pf in (_ = x) return exprT tvs x T with
       | eq_refl => val
       end =
       fun us vs =>
         val us match eq_sym pf in (_ = x) return hlist _ x with
                  | eq_refl => vs
                end.
  Proof.
    destruct pf; reflexivity.
  Qed.

  Definition exprT_UseV tus tvs (n : nat)
  : option { t : typ & exprT tus tvs (typD t) } :=
    match nth_error_get_hlist_nth _ tvs n with
      | None => None
      | Some (existT t get) =>
        Some (existT (fun t => exprT tus tvs (_ t)) t (fun _ vs => get vs))
    end.

  Definition exprT_UseU tus tvs (n : nat)
  : option { t : typ & exprT tus tvs (typD t) } :=
    match nth_error_get_hlist_nth _ tus n with
      | None => None
      | Some (existT t get) =>
        Some (existT (fun t => exprT tus tvs (_ t)) t (fun us _ => get us))
    end.

  Definition exprT_Inj tus tvs :=
    Eval simpl in @pure (exprT tus tvs)
                        (Applicative_exprT tus tvs).

  Hint Rewrite eq_exprT_eq eq_exprT_eq_F
       eq_exprT_eq_tus eq_exprT_eq_tvs : eq_rw.

  (** NOTE:
   ** - Right now this is intensionally weak, but it should probably include
   **   a few more operations given that it is already specialized for both
   **   [UVar] and [Var].
   ** - An alternative is to generalize it monadically and eliminate the
   **   specialized variable environments.
   ** - Note that this interface does not support GADTs
   **)
  Class Expr : Type :=
  { exprD' : forall (us vs : tenv typ),
               expr -> forall (t : typ),
                         option (exprT us vs (typD t))
  ; Expr_acc : relation expr
  ; wf_Expr_acc : well_founded Expr_acc
  ; mentionsAny : (uvar -> bool) -> (var -> bool) -> expr -> bool
  ; mentionsU : uvar -> expr -> bool
  ; mentionsV : var -> expr -> bool
  ; expr_subst
    : (uvar -> option expr) -> (var -> option expr) -> nat -> expr -> expr
  }.

  Definition exprD {E : Expr} (uvar_env var_env : env) (e : expr) (t : typ)
  : option (typD t) :=
    let (tus,us) := split_env uvar_env in
    let (tvs,vs) := split_env var_env in
    match exprD' tus tvs e t with
      | None => None
      | Some f => Some (f us vs)
    end.

  Theorem exprD'_conv (E : Expr)
  : forall tus tus' tvs tvs' e t
      (pfu : tus' = tus) (pfv : tvs' = tvs),
      exprD' tus tvs e t = match pfu in _ = tus'
                               , pfv in _ = tvs'
                                 return option (exprT tus' tvs' (typD t))
                           with
                             | eq_refl , eq_refl => exprD' tus' tvs' e t
                           end.
  Proof.
    destruct pfu. destruct pfv. reflexivity.
  Qed.

  Record ExprTApplicativeR (tus tvs tus' tvs' : tenv typ)
         (C : exprT tus tvs (exprT tus' tvs' Prop) -> Prop)
  : Type :=
  { exprTPureR : forall (P : exprT tus tvs (exprT tus' tvs' Prop)),
      (forall a b c d, P a b c d) -> C P
  ; exprTApR : forall P Q : exprT tus tvs (exprT tus' tvs' Prop),
        C (fun a b c d => P a b c d -> Q a b c d) -> C P -> C Q
  }.

  Definition expr_subst_spec_ho
             (exprD' : forall (us vs : tenv typ),
               expr -> forall (t : typ),
                         option (exprT us vs (typD t)))
             (expr_subst : (uvar -> option expr) -> (var -> option expr) -> nat -> expr -> expr)
  : Prop :=
    forall substU substV n e e',
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
                 eD us (HList.hlist_app _vs vs) = eD' us' (HList.hlist_app _vs vs')).

  Definition mentionsU_subst_spec
             (expr_subst : (uvar -> option expr) -> (var -> option expr) -> nat -> expr -> expr)
             (mentionsU : uvar -> expr -> bool)
             (mentionsV : var -> expr -> bool)
  : Prop :=
    forall substU substV n u e,
      mentionsU u (expr_subst substU substV n e) = true <->
      (   (mentionsU u e = true /\ substU u = None)
       \/ (exists u' e', mentionsU u' e = true /\
                         substU u' = Some e' /\
                         mentionsU u e' = true)
       \/ (exists v' e', mentionsV (n+v') e = true /\
                         substV v' = Some e' /\
                         mentionsU u e' = true)).

  Definition mentionsV_subst_spec
             (expr_subst : (uvar -> option expr) -> (var -> option expr) -> nat -> expr -> expr)
             (mentionsU : uvar -> expr -> bool)
             (mentionsV : var -> expr -> bool)
  : Prop :=
    forall substU substV n v e,
      mentionsV v (expr_subst substU substV n e) = true <->
      (   (v < n /\ mentionsV v e = true)
       \/ (v >= n /\
           (   (mentionsV v e = true /\ substV (v-n) = None)
            \/ (exists u' e', mentionsU u' e = true /\
                              substU u' = Some e' /\
                              mentionsV (v-n) e' = true)
            \/ (exists v' e', mentionsV (v'+n) e = true /\
                              substV v' = Some e' /\
                              mentionsV (v-n) e' = true)))).

  Class ExprOk (E : Expr) : Prop :=
  { exprD'_weaken
    : forall tus tvs e t val,
        exprD' tus tvs e t = Some val ->
        forall tus' tvs',
        exists val',
             exprD' (tus ++ tus') (tvs ++ tvs') e t = Some val'
          /\ forall us vs us' vs',
               val us vs = val' (hlist_app us us') (hlist_app vs vs')
  ; exprD'_strengthenU_single
    : forall tus tvs e t t' val,
      mentionsU (length tus) e = false ->
      exprD' (tus ++ t :: nil) tvs e t' = Some val ->
      exists val',
        exprD' tus tvs e t' = Some val' /\
        forall us vs u,
          val (hlist_app us (Hcons u Hnil)) vs = val' us vs
  ; exprD'_strengthenV_single
    : forall tus tvs e t t' val,
      mentionsV (length tvs) e = false ->
      exprD' tus (tvs ++ t :: nil) e t' = Some val ->
      exists val',
        exprD' tus tvs e t' = Some val' /\
        forall us vs u,
          val us (hlist_app vs (Hcons u Hnil)) = val' us vs
  ; Proper_mentionsAny
    : Proper ((eq ==> eq) ==> (eq ==> eq) ==> eq ==> eq) mentionsAny
  ; mentionsAny_weaken_strong
    : forall pu pu' pv pv' e,
        (forall u, mentionsU u e = true -> pu u = false -> pu' u = false) ->
        (forall v, mentionsV v e = true -> pv v = false -> pv' v = false) ->
        mentionsAny pu pv e = false ->
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
  ; expr_subst_sound_ho
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
  ; expr_subst_noop : forall substU substV n e,
      (forall u, mentionsU u e = true -> substU u = None) ->
      (forall v, mentionsV (v+n) e = true -> substV v = None) ->
      expr_subst substU substV n e = e
  ; mentionsU_subst
    : forall substU substV n u e,
      mentionsU u (expr_subst substU substV n e) = true <->
      (   (mentionsU u e = true /\ substU u = None)
       \/ (exists u' e', mentionsU u' e = true /\
                         substU u' = Some e' /\
                         mentionsU u e' = true)
       \/ (exists v' e', mentionsV (n+v') e = true /\
                         substV v' = Some e' /\
                         mentionsU u e' = true))
  ; mentionsV_subst
    : forall substU substV n v e,
      mentionsV v (expr_subst substU substV n e) = true <->
      (   (v < n /\ mentionsV v e = true)
       \/ (v >= n /\
           (   (mentionsV v e = true /\ substV (v-n) = None)
            \/ (exists u' e', mentionsU u' e = true /\
                              substU u' = Some e' /\
                              mentionsV (v-n) e' = true)
            \/ (exists v' e', mentionsV (v'+n) e = true /\
                              substV v' = Some e' /\
                              mentionsV (v-n) e' = true))))
  ; Proper_subst
    : Proper ((eq ==> eq) ==> (eq ==> eq) ==> eq ==> eq ==> eq) expr_subst
  }.

  Context {Expr_expr : Expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.

  Theorem mentionsAny_weaken
  : forall pu pu' pv pv',
      (forall u, pu u = false -> pu' u = false) ->
      (forall v, pv v = false -> pv' v = false) ->
      forall e, mentionsAny pu pv e = false ->
                mentionsAny pu' pv' e = false.
  Proof.
    intros. revert H1. eapply mentionsAny_weaken_strong; eauto.
  Qed.

  Lemma exprD'_weakenU
  : forall tus tus' tvs e t val,
      exprD' tus tvs e t = Some val ->
      exists val',
        exprD' (tus ++ tus') tvs e t = Some val'
        /\ forall us vs us',
             val us vs = val' (hlist_app us us') vs.
  Proof.
    intros.
    eapply (@exprD'_weaken Expr_expr) with (tus' := tus') (tvs' := nil) in H; eauto.
    destruct H as [ ? [ ? ? ] ].
    erewrite exprD'_conv with (tus' := tus ++ tus') (tvs' := tvs ++ nil).
    instantiate (1 := app_nil_r_trans _).
    instantiate (1 := eq_refl).
    simpl.
    rewrite H.
    exists (match
               app_nil_r_trans tvs in (_ = tvs')
               return (hlist _ (tus ++ tus') -> hlist _ tvs' -> typD t)
             with
               | eq_refl => x
             end).
    split.
    { clear. revert x. destruct (app_nil_r_trans tvs). reflexivity. }
    { intros. erewrite H0.
      instantiate (1 := Hnil).
      instantiate (1 := us').
      clear.
      rewrite hlist_app_nil_r at 1.
      revert x. revert vs. destruct (app_nil_r_trans tvs).
      reflexivity. }
  Qed.

  Lemma exprD'_weakenV
  : forall tus tvs tvs' e t val,
      exprD' tus tvs e t = Some val ->
      exists val',
        exprD' tus (tvs ++ tvs') e t = Some val'
        /\ forall us vs vs',
             val us vs = val' us (hlist_app vs vs').
  Proof.
    intros.
    eapply (@exprD'_weaken Expr_expr) with (tus' := nil) (tvs' := tvs') in H; eauto.
    destruct H as [ ? [ ? ? ] ].
    erewrite exprD'_conv with (tus' := tus ++ nil) (tvs' := tvs ++ tvs').
    instantiate (1 := @eq_refl _ _).
    instantiate (1 := app_nil_r_trans _).
    simpl.
    rewrite H.
    exists (match
               app_nil_r_trans tus in (_ = tus')
               return (hlist _ tus' -> _ -> typD t)
             with
               | eq_refl => x
             end).
    split.
    { clear. revert x. destruct (app_nil_r_trans tus). reflexivity. }
    { intros. erewrite H0.
      instantiate (1 := vs').
      instantiate (1 := Hnil).
      clear.
      rewrite hlist_app_nil_r at 1.
      revert x. revert us. destruct (app_nil_r_trans tus).
      reflexivity. }
  Qed.

  Theorem exprD_weaken
  : forall us us' vs vs' e t val,
      exprD us vs e t = Some val ->
      exprD (us ++ us') (vs ++ vs') e t = Some val.
  Proof.
    unfold exprD. intros.
    repeat rewrite split_env_app.
    destruct (split_env us); destruct (split_env us');
    destruct (split_env vs); destruct (split_env vs').
    consider (exprD' x x1 e t); intros; try congruence.
    inversion H0; clear H0; subst.
    eapply exprD'_weaken in H; eauto with typeclass_instances.
    destruct H. destruct H.
    rewrite H. rewrite <- H0. reflexivity.
  Qed.

  (** TODO: Move to ExtLib.Data.List. **)
  Lemma list_rev_ind
  : forall T (P : list T -> Prop),
      P nil ->
      (forall l ls, P ls -> P (ls ++ l :: nil)) ->
      forall ls, P ls.
  Proof.
    clear. intros. rewrite <- rev_involutive.
    induction (rev ls).
    apply H.
    simpl. auto.
  Qed.

  Theorem exprD'_strengthenV_multi
  : forall tus tvs e  t' tvs' val,
      (forall v, v < length tvs' ->
                 mentionsV (length tvs + v) e = false) ->
      exprD' tus (tvs ++ tvs') e t' = Some val ->
      exists val',
        exprD' tus tvs e t' = Some val' /\
        forall us vs vs',
          val us (hlist_app vs vs') = val' us vs.
  Proof.
    intros tus tvs e t'.
    refine (@list_rev_ind _ _ _ _).
    { simpl. intros.
      rewrite exprD'_conv with (pfv := app_nil_r_trans tvs) (pfu := eq_refl).
      rewrite H0. autorewrite with eq_rw.
      eexists; split; eauto.
      intros. rewrite (hlist_eta vs').
      rewrite hlist_app_nil_r.
      reflexivity. }
    { intros.
      rewrite exprD'_conv with (pfv := app_ass_trans tvs ls (l :: nil))
                               (pfu := eq_refl) in H1.
      autorewrite with eq_rw in H1.
      forward.
      eapply exprD'_strengthenV_single in H1.
      + forward_reason.
        eapply H in H1.
        - forward_reason.
          eexists; split; eauto.
          intros. inv_all; subst.
          clear - H3 H4.
          specialize (H4 us vs (fst (hlist_split _ _ vs'))).
          specialize (H3 us (hlist_app vs (fst (hlist_split _ _ vs')))
                         (hlist_hd (snd (hlist_split _ _ vs')))).
          rewrite <- H4; clear H4.
          rewrite <- H3; clear H3.
          autorewrite with eq_rw.
          f_equal.
          rewrite hlist_app_assoc.
          apply match_eq_match_eq.
          f_equal.
          etransitivity.
          symmetry.
          eapply (hlist_app_hlist_split _ _ vs').
          f_equal.
          rewrite (hlist_eta (snd (hlist_split _ _ _))).
          simpl. f_equal.
          rewrite (hlist_eta (hlist_tl _)). reflexivity.
        - intros.
          eapply H0. rewrite app_length. simpl. omega.
      + rewrite app_length.
        apply H0. rewrite app_length. simpl. omega. }
  Qed.

  Theorem exprD'_strengthenU_multi
  : forall tus tvs e  t' tus' val,
      (forall u, u < length tus' ->
                 mentionsU (length tus + u) e = false) ->
      exprD' (tus ++ tus') tvs e t' = Some val ->
      exists val',
        exprD' tus tvs e t' = Some val' /\
        forall us vs us',
          val (hlist_app us us') vs = val' us vs.
  Proof.
    intros tus tvs e t'.
    refine (@list_rev_ind _ _ _ _).
    { simpl. intros.
      rewrite exprD'_conv with (pfu := app_nil_r_trans tus) (pfv := eq_refl).
      rewrite H0. autorewrite with eq_rw.
      eexists; split; eauto.
      intros. rewrite (hlist_eta us').
      rewrite hlist_app_nil_r. reflexivity. }
    { intros.
      rewrite exprD'_conv with (pfu := app_ass_trans tus ls (l :: nil)) (pfv := eq_refl) in H1.
      autorewrite with eq_rw in H1.
      forward.
      eapply exprD'_strengthenU_single in H1.
      + forward_reason.
        eapply H in H1.
        - forward_reason.
          eexists; split; eauto.
          intros. inv_all; subst.
          clear - H3 H4.
          specialize (H4 us vs (fst (hlist_split _ _ us'))).
          specialize (H3 (hlist_app us (fst (hlist_split _ _ us')))
                         vs (hlist_hd (snd (hlist_split _ _ us')))).
          rewrite <- H4; clear H4.
          rewrite <- H3; clear H3.
          repeat rewrite eq_Arr_eq. repeat rewrite eq_Const_eq.
          f_equal.
          rewrite hlist_app_assoc.
          autorewrite with eq_rw.
          f_equal.
          eapply match_eq_match_eq.
          f_equal.
          etransitivity. symmetry. eapply (hlist_app_hlist_split _ _ us').
          f_equal.
          rewrite (hlist_eta (snd (hlist_split _ _ _))).
          simpl. f_equal.
          rewrite (hlist_eta (hlist_tl _)). reflexivity.
        - intros.
          eapply H0. rewrite app_length. simpl. omega.
      + rewrite app_length.
        apply H0. rewrite app_length. simpl. omega. }
  Qed.

  Theorem expr_subst_sound
  : forall substU substV n e e',
      expr_subst substU substV n e = e' ->
      forall _tvs tus tvs tus' tvs'
             (R : exprT tus tvs (exprT tus' tvs' Prop))
             (H_substU : forall u t get,
                 nth_error_get_hlist_nth typD tus u = Some (@existT _ _ t get) ->
                 match substU u with
                   | Some eU =>
                     exists eUD,
                     exprD' tus' tvs' eU t = Some eUD /\
                     forall us vs us' vs',
                       R us vs us' vs' -> get us = eUD us' vs'
                   | None =>
                     exists get',
                        nth_error_get_hlist_nth typD tus' u = Some (@existT _ _ t get')
                     /\ forall us vs us' vs', R us vs us' vs' -> get us = get' us'
                 end)
             (H_substV : forall u t get,
                 nth_error_get_hlist_nth typD tvs u = Some (@existT _ _ t get) ->
                 match substV u with
                   | Some eV =>
                     exists eVD,
                     exprD' tus' tvs' eV t = Some eVD /\
                     forall us vs us' vs', R us vs us' vs' -> get vs = eVD us' vs'
                   | None => exists get',
                             nth_error_get_hlist_nth typD tvs' u = Some (@existT _ _ t get')
                             /\ forall us vs us' vs', R us vs us' vs' -> get vs = get' vs'
                 end),
      forall t eD,
        length _tvs = n ->
        exprD' tus (_tvs ++ tvs) e t = Some eD ->
        exists eD',
          exprD' tus' (_tvs ++ tvs') e' t = Some eD' /\
          forall us vs us' vs' _vs, R us vs us' vs' ->
                 eD us (HList.hlist_app _vs vs) = eD' us' (HList.hlist_app _vs vs').
  Proof.
    intros.
    eapply (@expr_subst_sound_ho) in H1; eauto with typeclass_instances.
    2: instantiate (1 := fun P => forall us vs us' vs', R us vs us' vs' -> P us vs us' vs').
    { forward_reason.
      eexists; split; eauto. }
    { constructor.
      { intros. eauto. }
      { intros. eauto. } }
    eauto. eauto.
  Qed.

  Corollary mentionsAny_complete_false
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

End Expr.

(* Arguments Safe_expr {_ _ _ Expr} _ _ _ _ : rename. *)
Arguments exprD' {_ _ _ Expr} _ _ _ _ : rename.
Arguments exprD {_ _ _ Expr} _ _ _ _ : rename.
Arguments exprT {_ RType} _ _ _ : rename.
Arguments exprT_Inj {_ _} _ _ {_} _ _ _ : rename.
Arguments exprT_UseU {_ _} tus tvs n : rename.
Arguments exprT_UseV {_ _} tus tvs n : rename.
Arguments RexprT {typ RType} tus tvs {_} _ _ _ : rename.
Arguments mentionsAny {typ RType expr Expr} _ _ _ : rename.

Export MirrorCore.TypesI.
Export MirrorCore.EnvI.
Export MirrorCore.OpenT.

Hint Rewrite eq_exprT_eq eq_exprT_eq_F
     eq_exprT_eq_tus eq_exprT_eq_tvs : eq_rw.
