Require Import Coq.Lists.List.
Require Import Relations.Relation_Definitions.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.OpenT.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.EnvI.

Set Implicit Arguments.
Set Strict Implicit.

Section Expr.
  Variable typ : Type.
  Variable RType_typ : RType typ.

  Variable expr : Type.

  Record ctyp := mkctyp
  { cctx : list typ ; vtyp : typ }.

  Definition ctxD (ctx : ctyp) : Type :=
    OpenT typD ctx.(cctx) (typD ctx.(vtyp)).

  Definition exprT (us : tenv ctyp) (vs : tenv typ) (T : Type) : Type :=
    OpenT ctxD us (OpenT typD vs T).

  Definition Applicative_exprT tus tvs : Applicative (exprT tus tvs) :=
    Eval cbv beta iota zeta delta [ ap pure Applicative_OpenT ] in
  {| pure := fun _ x => pure (pure x)
  ; ap := fun _ _ f x => ap (T:=OpenT ctxD tus)
         (ap (T:=OpenT ctxD tus) (pure (ap (T:=OpenT typD tvs))) f) x
  |}.
  Existing Instance Applicative_exprT.

  Definition Functor_exprT tus tvs : Functor (exprT tus tvs) :=
    Eval cbv beta iota zeta delta [ fmap Functor_OpenT ] in
  {| fmap := fun _ _ f x => fmap (fmap f) x
  |}.
  Existing Instance Functor_exprT.

  (** NOTE:
   ** - Right now this is intensionally weak, but it should probably include
   **   a few more operations given that it is already specialized for both
   **   [UVar] and [Var].
   ** - An alternative is to generalize it monadically and eliminate the
   **   specialized variable environments.
   ** - Note that this interface does not support GADTs
   **)
  Class Expr : Type :=
  { exprD' : forall (us : tenv ctyp) (vs : tenv typ),
               expr -> forall (t : typ),
                         option (exprT us vs (typD t))
  ; Expr_acc : relation expr
  ; wf_Expr_acc : well_founded Expr_acc
(*
  ; mentionsU : nat -> expr -> bool
  ; mentionsV : nat -> expr -> bool
*)
  }.

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

  Definition Safe_expr {E : Expr} (tus : tenv ctyp) (tvs : tenv typ) (e : expr) (t : typ)
  : Prop :=
    exists val, exprD' tus tvs e t = Some val.

  Theorem Safe_expr_exprD {E : Expr}
  : forall us vs e t,
      Safe_expr us vs e t <->
      exists val, exprD' us vs e t = Some val.
  Proof. reflexivity. Qed.

  Definition exprD {E : Expr} uvar_env (var_env : env typD) (e : expr) (t : typ)
  : option (typD t) :=
    let (tus,us) := split_env uvar_env in
    let (tvs,vs) := split_env var_env in
    match exprD' tus tvs e t with
      | None => None
      | Some f => Some (f us vs)
    end.

  Class ExprOk (E : Expr) : Type :=
  { exprD'_weaken
    : forall tus tvs e t val,
        exprD' tus tvs e t = Some val ->
        forall tus' tvs',
        exists val',
             exprD' (tus ++ tus') (tvs ++ tvs') e t = Some val'
          /\ forall us vs us' vs',
               val us vs = val' (hlist_app us us') (hlist_app vs vs')
(*
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
*)
  }.

  Context {Expr_expr : Expr}.

  Lemma exprD'_weakenU (EOk : ExprOk Expr_expr)
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

  Lemma exprD'_weakenV (EOk : ExprOk Expr_expr)
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

  Theorem exprD_weaken (EOk : ExprOk Expr_expr)
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

(*

  Theorem exprD'_strengthenU_multi (EOk : ExprOk Expr_expr)
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
      rewrite H0.
      unfold ResType. rewrite eq_option_eq.
      eexists; split; eauto.
      intros. rewrite (hlist_eta us').
      rewrite hlist_app_nil_r.
      clear.
      repeat first [ rewrite eq_Const_eq | rewrite eq_Arr_eq ].
      reflexivity. }
    { intros.
      rewrite exprD'_conv with (pfu := app_ass_trans tus ls (l :: nil)) (pfv := eq_refl) in H1.
      unfold ResType in H1. rewrite eq_option_eq in H1.
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
          apply match_eq_match_eq.
          f_equal.
          etransitivity.
          symmetry.
          eapply (hlist_app_hlist_split _ _ us').
          f_equal.
          rewrite (hlist_eta (snd (hlist_split _ _ _))).
          simpl. f_equal.
          rewrite (hlist_eta (hlist_tl _)). reflexivity.
        - intros.
          eapply H0. rewrite app_length. simpl. omega.
      + rewrite app_length.
        apply H0. rewrite app_length. simpl. omega. }
  Qed.


  Theorem exprD'_strengthenV_multi (EOk : ExprOk Expr_expr)
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
      rewrite H0.
      unfold ResType. rewrite eq_option_eq.
      eexists; split; eauto.
      intros. rewrite (hlist_eta vs').
      rewrite hlist_app_nil_r.
      clear.
      repeat first [ rewrite eq_Const_eq | rewrite eq_Arr_eq ].
      reflexivity. }
    { intros.
      rewrite exprD'_conv with (pfv := app_ass_trans tvs ls (l :: nil)) (pfu := eq_refl) in H1.
      unfold ResType in H1. rewrite eq_option_eq in H1.
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
          repeat rewrite eq_Arr_eq. repeat rewrite eq_Const_eq.
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
*)
End Expr.

Arguments Safe_expr {_ _ _ Expr} _ _ _ _ : rename.
Arguments exprD' {_ _ _ Expr} _ _ _ _ : rename.
Arguments exprD {_ _ _ Expr} _ _ _ _ : rename.
Arguments exprT {_ RType} _ _ _ : rename.
(*
Arguments mentionsU {_ RType _ Expr} _ _ : rename.
Arguments mentionsV {_ RType _ Expr} _ _ : rename.
*)
Arguments ctxD {typ _} _ : rename.
