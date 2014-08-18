Require Import Coq.Lists.List.
Require Import Relations.Relation_Definitions.
Require Import ExtLib.Tactics.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Eq.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.EnvI.

Set Implicit Arguments.
Set Strict Implicit.

Section Expr.
  Variable typ : Type.
  Variable RType_typ : RType typ.

  Variable expr : tenv typ -> tenv typ -> typ -> Type.

  Definition OpenT (us vs : tenv typ) (T : Type) : Type :=
    hlist (typD nil) us -> hlist (typD nil) vs -> T.

  Definition ResType (us vs : tenv typ) (T : Type) : Type :=
    option (OpenT us vs T).

  Lemma eq_ResType_eq_us
  : forall tus tus' tvs T (pf : tus = tus') v,
      match pf in _ = x return ResType x tvs T with
        | eq_refl => v
      end =
      match v with
        | None => None
        | Some res => Some
          match pf in _ = x return OpenT x tvs T with
            | eq_refl => res
          end
      end.
  Proof.
    destruct pf; destruct v; reflexivity.
  Qed.
  Lemma eq_ResType_eq_vs
  : forall tus tvs tvs' T (pf : tvs = tvs') v,
      match pf in _ = x return ResType tus x T with
        | eq_refl => v
      end =
      match v with
        | None => None
        | Some res => Some
          match pf in _ = x return OpenT tus x T with
            | eq_refl => res
          end
      end.
  Proof.
    destruct pf; destruct v; reflexivity.
  Qed.
  Lemma eq_OpenT_eq_us
  : forall tus tus' tvs T (pf : tus = tus') v us vs,
      match pf in _ = x return OpenT x tvs T with
        | eq_refl => v
      end us vs =
      v match eq_sym pf in _ = x return hlist (typD nil) x with
          | eq_refl => us
        end vs.
  Proof. destruct pf. reflexivity. Qed.
  Lemma eq_OpenT_eq_vs
  : forall tus tvs tvs' T (pf : tvs = tvs') v us vs,
      match pf in _ = x return OpenT tus x T with
        | eq_refl => v
      end us vs =
      v us match eq_sym pf in _ = x return hlist (typD nil) x with
             | eq_refl => vs
           end.
  Proof. destruct pf. reflexivity. Qed.
  Hint Rewrite eq_ResType_eq_us eq_ResType_eq_vs : eq_rw.
  Hint Rewrite eq_OpenT_eq_us eq_OpenT_eq_vs : eq_rw.

  (** NOTE:
   ** - An alternative is to generalize it monadically and eliminate the
   **   specialized variable environments.
   ** - Note that this interface does not support GADTs
   **)
  Class Expr : Type :=
  { exprD' : forall (tus tvs : tenv typ) (t : typ),
               expr tus tvs t -> ResType tus tvs (typD nil t)
(*
  ; Expr_acc : relation expr
  ; wf_Expr_acc : well_founded Expr_acc
*)
  ; mentionsU
    : forall (tus tvs : tenv typ) (t : typ), nat -> expr tus tvs t -> bool
  ; mentionsV
    : forall (tus tvs : tenv typ) (t : typ), nat -> expr tus tvs t -> bool
  ; weaken
    : forall (tus tvs : tenv typ ) (t : typ)
             (tus' tvs' : tenv typ),
        expr tus tvs t -> expr (tus ++ tus') (tvs ++ tvs') t
  ; strengthen
    : forall (tus tvs : tenv typ) (t : typ)
             (tus' tvs' : tenv typ),
        expr (tus ++ tus') (tvs ++ tvs') t -> option (expr tus tvs t)
  }.
  Arguments exprD' {Expr} tus tvs t e : rename.

  (* NOTE: these could all be more efficient... *)
  Definition strengthenU (E : Expr) (tus tvs : tenv typ) t (tus' : tenv typ)
             (e : expr (tus ++ tus') tvs t)
  : option (expr tus tvs t) :=
    let e :=
        match eq_sym (app_nil_r_trans tvs) in _ = T
              return expr (tus ++ tus') T t
        with
          | eq_refl => e
        end
    in
    @strengthen E tus tvs t tus' nil e.

  Definition strengthenV (E : Expr) (tus tvs : tenv typ) t (tvs' : tenv typ)
             (e : expr tus (tvs ++ tvs') t)
  : option (expr tus tvs t) :=
    let e :=
        match eq_sym (app_nil_r_trans tus) in _ = T
              return expr T (tvs ++ tvs') t
        with
          | eq_refl => e
        end
    in
    @strengthen E tus tvs t nil tvs' e.

  Definition weakenU (E : Expr) (tus tvs : tenv typ) t (tus' : tenv typ)
             (e : expr tus tvs t)
  : expr (tus ++ tus') tvs t :=
    match app_nil_r_trans tvs in _ = T
          return expr (tus ++ tus') T t
    with
      | eq_refl => (@weaken E tus tvs t tus' nil e)
    end.

  Definition weakenV (E : Expr) (tus tvs : tenv typ) t (tvs' : tenv typ)
             (e : expr tus tvs t)
  : expr tus (tvs ++ tvs') t :=
    match app_nil_r_trans tus in _ = T
          return expr T (tvs ++ tvs') t
    with
      | eq_refl => (@weaken E tus tvs t nil tvs' e)
    end.

  Theorem exprD'_conv (E : Expr)
  : forall tus tus' tvs tvs' t (e : expr tus tvs t)
      (pfu : tus' = tus) (pfv : tvs' = tvs),
      exprD' tus tvs t e = match pfu in _ = tus'
                               , pfv in _ = tvs'
                                 return expr tus' tvs' t -> ResType tus' tvs' (typD nil t)
                           with
                             | eq_refl , eq_refl =>
                               exprD' tus' tvs' t
                           end e.
  Proof.
    destruct pfu. destruct pfv. reflexivity.
  Defined.

  Definition Safe_expr {E : Expr} (tus tvs : tenv typ) (t : typ)
             (e : expr tus tvs t)
  : Prop :=
    exists val, exprD' tus tvs t e = Some val.
  Arguments Safe_expr {Expr} tus tvs t e : rename.

  Theorem Safe_expr_exprD {E : Expr}
  : forall tus tvs t (e : expr tus tvs t),
      Safe_expr tus tvs t e <->
      exists val, exprD' tus tvs t e = Some val.
  Proof. reflexivity. Qed.

(*
  Definition exprD {E : Expr} (uvar_env var_env : env nil) (t : typ)
             (e : expr)
  : option (typD nil t) :=
    let (tus,us) := split_env uvar_env in
    let (tvs,vs) := split_env var_env in
    match exprD' tus tvs t e with
      | None => None
      | Some f => Some (f us vs)
    end.
*)

  Class ExprOk (E : Expr) : Type :=
  { exprD'_weaken
    : forall tus tvs t (e:expr tus tvs t) val,
        exprD' tus tvs t e = Some val ->
        forall tus' tvs',
        exists val',
             exprD' (tus ++ tus') (tvs ++ tvs') t (weaken tus' tvs' e) = Some val'
          /\ forall us vs us' vs',
               val us vs = val' (hlist_app us us') (hlist_app vs vs')
  ; exprD'_strengthenU_single
    : forall tus tvs t t' (e : expr (tus ++ t :: nil) tvs t') val,
      mentionsU (length tus) e = false ->
      exprD' (tus ++ t :: nil) tvs t' e = Some val ->
      exists val' (e' : expr tus tvs t'),
        @strengthenU E tus tvs t' (t :: nil) e = Some e' /\
        exprD' tus tvs t' e' = Some val' /\
        forall us vs u,
          val (hlist_app us (Hcons u Hnil)) vs = val' us vs
  ; exprD'_strengthenV_single
    : forall tus tvs t t' (e:expr tus (tvs ++ t :: nil) t') val,
      mentionsV (length tvs) e = false ->
      exprD' tus (tvs ++ t :: nil) t' e = Some val ->
      exists val' (e' : expr tus tvs t'),
        @strengthenV E tus tvs t' (t :: nil) e = Some e' /\
        exprD' tus tvs t' e' = Some val' /\
        forall us vs u,
          val us (hlist_app vs (Hcons u Hnil)) = val' us vs
  }.

  Context {Expr_expr : Expr}.

  Lemma exprD'_weakenU (EOk : ExprOk Expr_expr)
  : forall tus tus' tvs t e val,
      exprD' tus tvs t e = Some val ->
      exists val',
        exprD' (tus ++ tus') tvs t (weakenU _ tus' e) = Some val'
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
    unfold weakenU.
    autorewrite with eq_rw.
    rewrite H.
    eexists; split; [ reflexivity | ].
    intros. specialize (H0 us vs us' Hnil).
    rewrite H0. rewrite hlist_app_nil_r.
    autorewrite with eq_rw. reflexivity.
  Qed.

  Lemma exprD'_weakenV (EOk : ExprOk Expr_expr)
  : forall tus tvs tvs' t e val,
      exprD' tus tvs t e = Some val ->
      exists val',
        exprD' tus (tvs ++ tvs') t (weakenV _ tvs' e) = Some val'
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
    unfold weakenV.
    autorewrite with eq_rw.
    rewrite H. eexists; split; [ reflexivity | ].
    intros.
    rewrite (H0 us vs Hnil vs').
    rewrite hlist_app_nil_r.
    autorewrite with eq_rw.
    reflexivity.
  Qed.
(*
  Theorem exprD_weaken (EOk : ExprOk Expr_expr)
  : forall us us' vs vs' e t val,
      exprD us vs t e = Some val ->
      exprD (us ++ us') (vs ++ vs') t e = Some val.
  Proof.
    unfold exprD. intros.
    repeat rewrite split_env_app.
    destruct (split_env us); destruct (split_env us');
    destruct (split_env vs); destruct (split_env vs').
    consider (exprD' x x1 t e); intros; try congruence.
    inversion H0; clear H0; subst.
    eapply exprD'_weaken in H; eauto with typeclass_instances.
    destruct H. destruct H.
    rewrite H. rewrite <- H0. reflexivity.
  Qed.
*)

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
  : forall tus tvs e t' tus' val,
      (forall u, u < length tus' ->
                 mentionsU (length tus + u) e = false) ->
      exprD' (tus ++ tus') tvs t' e = Some val ->
      exists val',
        exprD' tus tvs t' e = Some val' /\
        forall us vs us',
          val (hlist_app us us') vs = val' us vs.
  Proof.
    intros tus tvs e t'.
    refine (@list_rev_ind _ _ _ _).
    { simpl. intros.
      rewrite exprD'_conv with (pfu := app_nil_r_trans tus) (pfv := eq_refl).
      rewrite H0.
      autorewrite with eq_rw.
      eexists; split; eauto.
      intros. rewrite (hlist_eta us').
      rewrite hlist_app_nil_r.
      clear.
      autorewrite with eq_rw. reflexivity. }
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
          autorewrite with eq_rw.
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
      exprD' tus (tvs ++ tvs') t' e = Some val ->
      exists val',
        exprD' tus tvs t' e = Some val' /\
        forall us vs vs',
          val us (hlist_app vs vs') = val' us vs.
  Proof.
    intros tus tvs e t'.
    refine (@list_rev_ind _ _ _ _).
    { simpl. intros.
      rewrite exprD'_conv with (pfv := app_nil_r_trans tvs) (pfu := eq_refl).
      rewrite H0.
      autorewrite with eq_rw.
      eexists; split; eauto.
      intros. rewrite (hlist_eta vs').
      rewrite hlist_app_nil_r.
      clear.
      autorewrite with eq_rw.
      reflexivity. }
    { intros.
      rewrite exprD'_conv with (pfv := app_ass_trans tvs ls (l :: nil)) (pfu := eq_refl) in H1.
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
          rewrite <- (hlist_app_hlist_split _ _ vs') at 1.
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
(*Arguments exprD {_ _ _ Expr} _ _ _ _ : rename. *)
Arguments ResType {_ RType} _ _ _ : rename.
Arguments mentionsU {_ RType _ Expr} _ _ _ _ _ : rename.
Arguments mentionsV {_ RType _ Expr} _ _ _ _ _ : rename.
