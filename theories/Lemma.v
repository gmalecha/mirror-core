Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.OpenT.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.Util.ListMapT.
Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section lem.
  Variable typ : Type.
  Variable RType_typ : RType typ.
  Variable expr : Type.
  Variable conclusion : Type.
  Context {Expr_expr : Expr _ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.

  Record lemma : Type := Build_lemma
  { vars : list typ
  ; premises : list expr
  ; concl : conclusion
  }.

  Variable conclusionD : forall us vs, conclusion -> option (exprT us vs Prop).

  Fixpoint foralls (ls : list typ) : (OpenT typD ls Prop) -> Prop :=
    match ls as ls return (OpenT typD ls Prop) -> Prop with
      | nil => fun P => P Hnil
      | l :: ls => fun P => forall x : typD l,
                              foralls (fun z => P (Hcons x z))
    end.

  Lemma foralls_sem : forall ls P,
    foralls (ls := ls) P <-> forall h, P h.
  Proof.
    clear.
    induction ls; simpl; intros.
    { intuition; rewrite hlist_eta; auto. }
    { intuition.
      { rewrite hlist_eta.
        specialize (H (hlist_hd h)).
        rewrite IHls in H. eauto. }
      { rewrite IHls. intuition. } }
  Qed.

  Lemma foralls_iff
  : forall ls F G,
      (forall x, (F x) <-> (G x)) ->
      ((@foralls ls F) <-> (@foralls ls G)).
  Proof.
    intros.
    rewrite foralls_sem. rewrite foralls_sem.
    intuition; eapply H; eauto.
  Qed.

  Lemma foralls_impl
  : forall ls (F G : _ -> Prop),
      (forall x, (F x) -> (G x)) ->
      ((@foralls ls F) -> (@foralls ls G)).
  Proof.
    intros.
    rewrite foralls_sem. rewrite foralls_sem in H0.
    intuition; eapply H; eauto.
  Qed.

  Fixpoint impls (ls : list Prop) (P : Prop) :=
    match ls with
      | nil => P
      | l :: ls => l -> impls ls P
    end.

  Lemma impls_sem : forall ps x,
    impls ps x <->
    (Forall (fun x => x) ps -> x).
  Proof.
    induction ps; simpl; intuition.
    { inversion H0; clear H0; subst.
      eapply IHps; auto. }
    { eapply IHps. intros. eapply H. constructor; auto. }
  Qed.

  Lemma impls_iff : forall ps ps' p q,
                      Forall2 (fun P Q => P <-> Q) ps ps' ->
                      (p <-> q) ->
                      (@impls ps p <-> @impls ps' q).
  Proof.
    clear.
    induction 1; simpl; intros; auto.
    rewrite H. rewrite IHForall2; eauto. reflexivity.
  Qed.

  Definition lemmaD' tus (tvs : tenv typ) (l : lemma)
  : option (exprT tus tvs Prop) :=
    match
        Traversable.mapT (T := list) (F := option)
                         (exprD'_typ0 Prop tus (vars l ++ tvs))
                         (premises l)
      , conclusionD tus (vars l ++ tvs) (concl l)
    with
      | Some prems , Some concl =>
        Some (fun us vs =>
                foralls (fun h : hlist (typD) (vars l) =>
                           let vs' := hlist_app h vs in
                           impls (map (fun x => x us vs') prems)
                                 (concl us vs')))
      | _ , _ => None
    end.

  Lemma lemmaD'_conv
  : forall l tus tvs tus' tvs' (pfu : tus' = tus) (pfv : tvs' = tvs),
      lemmaD' tus tvs l =
      match pfu in _ = tu' , pfv in _ = tv'
            return option (exprT tu' tv' Prop)
      with
        | eq_refl , eq_refl => lemmaD' tus' tvs' l
      end.
  Proof.
    clear. intros; subst. reflexivity.
  Qed.

  Hypothesis conclusionD_weaken
  : forall tus tvs l lD,
      conclusionD tus tvs l = Some lD ->
      forall tus' tvs',
        exists lD',
          conclusionD (tus ++ tus') (tvs ++ tvs') l = Some lD' /\
          forall us vs us' vs',
            lD us vs <-> lD' (hlist_app us us') (hlist_app vs vs').
(*
  Hypothesis conclusionD_weakenV
  : forall tus tvs l lD,
      conclusionD tus tvs l = Some lD ->
      forall tvs',
        exists lD',
          conclusionD tus (tvs ++ tvs') l = Some lD' /\
          forall us vs vs',
            lD us vs <-> lD' us (hlist_app vs vs').
*)

  Lemma Forall2_map1
  : forall T U V (f : T -> V) (R : V -> U -> Prop)
           ls ls',
      Forall2 R (map f ls) ls' <->
      Forall2 (fun x y => R (f x) y) ls ls'.
  Proof.
    clear. induction ls; simpl.
    { split; inversion 1; subst; auto. }
    { split; inversion 1; subst.
      { inversion H. subst. constructor; auto. eapply IHls. eauto. }
      { inversion H. subst. constructor; auto. eapply IHls. eauto. } }
  Qed.

  Lemma Forall2_map2
  : forall T U V (f : T -> _) (R : V -> U -> Prop)
           ls ls',
      Forall2 R ls (map f ls') <->
      Forall2 (fun x y => R x (f y)) ls ls'.
  Proof.
    clear. induction ls; simpl.
    { split; inversion 1; subst; auto.
      destruct ls'. auto. inversion H0. constructor. }
    { split; inversion 1; subst. destruct ls'; [ inversion H2 | ].
      simpl in *. inversion H2; clear H2; subst.
      { inversion H. subst. constructor; auto. eapply IHls. eauto. }
      { inversion H. subst. constructor; auto. eapply IHls. eauto. } }
  Qed.

  Lemma lemmaD'_weaken
  : forall tus tvs l lD,
      lemmaD' tus tvs l = Some lD ->
      forall tus' tvs',
        exists lD',
          lemmaD' (tus ++ tus') (tvs ++ tvs') l = Some lD' /\
          forall us us' vs vs',
            lD us vs <-> lD' (hlist_app us us') (hlist_app vs vs').
  Proof.
    unfold lemmaD'; simpl; intros.
    forward; inv_all; subst.
    specialize (@conclusionD_weaken _ _ _ _ H0 tus' tvs'); clear H0.
    destruct conclusionD_weaken as [ ? [ ? ? ] ]; clear conclusionD_weaken.
    match goal with
      | |- exists x , match ?X with _ => _ end = _ /\ _ =>
        cutrewrite (X = match app_ass_trans (vars l) tvs tvs' in _ = t
                          return option (list (exprT (tus ++ tus') t Prop))
                    with
                      | eq_refl =>
                        mapT (exprD'_typ0 Prop (tus ++ tus') ((vars l ++ tvs) ++ tvs'))
                             (premises l)
                    end)
    end.
    match goal with
      | |- exists x , match _ with Some _ => match ?X with _ => _ end | None => _ end = _ /\ _ =>
        cutrewrite (X = match app_ass_trans (vars l) tvs tvs' in _ = t
                          return option (exprT (tus ++ tus') t Prop)
                        with
                          | eq_refl =>
                            conclusionD (tus ++ tus') ((vars l ++ tvs) ++ tvs') l.(concl)
                        end)
    end.
    { rewrite H0; clear H0.
      clear - ExprOk_expr H H1. generalize dependent l0.
      admit. }
    { clear.
      generalize (app_ass_trans (vars l) tvs tvs').
      generalize ((vars l ++ tvs) ++ tvs').
      intros; subst. reflexivity. }
    { clear.
      generalize (app_ass_trans (vars l) tvs tvs').
      generalize ((vars l ++ tvs) ++ tvs').
      intros; subst. reflexivity. }
  Qed.

  Lemma lemmaD'_weakenV
  : forall tus tvs l lD,
      lemmaD' tus tvs l = Some lD ->
      forall tvs',
        exists lD',
          lemmaD' tus (tvs ++ tvs') l = Some lD' /\
          forall us vs vs',
            lD us vs <-> lD' us (hlist_app vs vs').
  Proof.
    intros.
    destruct (@lemmaD'_weaken tus tvs _ _ H nil tvs') as [ ? [ ? ?  ] ].
    rewrite lemmaD'_conv with (pfu := eq_sym (app_nil_r_trans _)) (pfv := eq_refl) in H0.
    unfold exprT, OpenT in H0.
    autorewrite with eq_rw in H0.
    forwardy; inv_all; subst.
    eexists; split; eauto.
    intros. rewrite (H1 us Hnil vs vs').
    rewrite hlist_app_nil_r.
    clear.
    destruct (eq_sym (app_nil_r_trans tus)). reflexivity.
  Qed.

  Lemma lemmaD'_weakenU
  : forall tus tvs l lD,
      lemmaD' tus tvs l = Some lD ->
      forall tus',
        exists lD',
          lemmaD' (tus ++ tus') tvs l = Some lD' /\
          forall us vs us',
            lD us vs <-> lD' (hlist_app us us') vs.
  Proof.
    intros.
    destruct (@lemmaD'_weaken tus tvs _ _ H tus' nil) as [ ? [ ? ?  ] ].
    rewrite lemmaD'_conv with (pfv := eq_sym (app_nil_r_trans _)) (pfu := eq_refl) in H0.
    unfold exprT, OpenT in H0.
    autorewrite with eq_rw in H0.
    forwardy; inv_all; subst.
    eexists; split; eauto.
    intros. rewrite (H1 us us' vs Hnil).
    rewrite hlist_app_nil_r.
    clear.
    destruct (eq_sym (app_nil_r_trans tvs)). reflexivity.
  Qed.

  Definition lemmaD us (vs : env _) (l : lemma) : Prop :=
    let (tus,us) := split_env us in
    let (tvs,vs) := split_env vs in
    match lemmaD' tus tvs l with
      | None => False
      | Some P => P us vs
    end.

  Lemma lemmaD_weakenU
  : forall us us' vs l,
      lemmaD us vs l ->
      lemmaD (us ++ us') vs l.
  Proof.
    intros.
    unfold lemmaD in H. forward.
    red. rewrite split_env_app.
    Cases.rewrite_all_goal.
    forward. inv_all. subst. subst.
    eapply lemmaD'_weakenU with (tus' := x2) in H1.
    destruct H1 as [ ? [ ? ? ] ].
    rewrite H1. apply H4. assumption.
  Qed.

  Lemma lemmaD_weakenV
  : forall us vs vs' l,
      lemmaD us vs l ->
      lemmaD us (vs ++ vs') l.
  Proof.
    intros.
    unfold lemmaD in H. forward.
    red. rewrite split_env_app.
    Cases.rewrite_all_goal.
    forward. inv_all. subst. subst.
    eapply lemmaD'_weakenV with (tvs' := x2) in H1.
    destruct H1 as [ ? [ ? ? ] ].
    rewrite H1. apply H4. assumption.
  Qed.

End lem.
