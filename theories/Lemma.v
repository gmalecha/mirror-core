Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Util.ListMapT.

Set Implicit Arguments.
Set Strict Implicit.

Section lem.
  Variable typ : Type.
  Variable RType_typ : RType typ.
  Variable expr : Type.
  Variable Expr_expr : Expr _ expr.
  Hypothesis ExprOk_expr : ExprOk Expr_expr.
  Variable conclusion : Type.

  Record lemma : Type := Build_lemma
  { vars : list typ
  ; premises : list expr
  ; concl : conclusion
  }.

  Variable conclusionD : forall us vs, conclusion -> option (exprT us vs Prop).

  Context {tyProp : typ}.
  Variable Provable' : typD tyProp -> Prop.

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

  Definition lemmaD' (tus tvs : tenv typ) (l : lemma)
  : option (exprT tus tvs Prop) :=
    match
        Traversable.mapT (T := list) (F := option)
                         (fun e : expr => exprD' tus (vars l ++ tvs) e tyProp)
                         (premises l)
      , conclusionD tus (vars l ++ tvs) (concl l)
    with
      | Some prems , Some concl =>
        Some (fun us vs =>
                foralls (fun h : hlist (typD) (vars l) =>
                           let vs' := hlist_app h vs in
                           impls (map (fun x => Provable' (x us vs')) prems)
                                 (concl us vs')))
      | _ , _ => None
    end.

  Hypothesis conclusionD_weakenU
  : forall tus tvs l lD,
      conclusionD tus tvs l = Some lD ->
      forall tus',
        exists lD',
          conclusionD (tus ++ tus') tvs l = Some lD' /\
          forall us us' vs,
            lD us vs <-> lD' (hlist_app us us') vs.
  Hypothesis conclusionD_weakenV
  : forall tus tvs l lD,
      conclusionD tus tvs l = Some lD ->
      forall tvs',
        exists lD',
          conclusionD tus (tvs ++ tvs') l = Some lD' /\
          forall us vs vs',
            lD us vs <-> lD' us (hlist_app vs vs').

  Opaque Traversable.mapT.

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

  Lemma lemmaD'_weakenU
  : forall tus tvs l lD,
      lemmaD' tus tvs l = Some lD ->
      forall tus',
        exists lD',
          lemmaD' (tus ++ tus') tvs l = Some lD' /\
          forall us us' vs,
            lD us vs <-> lD' (hlist_app us us') vs.
  Proof.
(*
    unfold lemmaD'; simpl; intros.
    forward.
    inv_all; subst.
    generalize (fun H' =>
                  @mapT_Forall2 _ _
                                 (fun e v =>
                                    exists v',
                                      exprD' (tus ++ tus') (vars l ++ tvs) e tyProp = Some v' /\
                                      forall a b c,
                                        v a b = v' (hlist_app a c) b)
                   _
                   H'
                   _ _ H).
    match goal with
      | |- (?X -> _) -> _ =>
        let H := fresh in
        assert (H : X) ;
          [ | intro XXX; specialize (XXX H) ]
    end.
    { simpl. intros.
      eapply exprD'_weakenU with (tus' := tus') (t := tyProp) in H1;
        eauto with typeclass_instances. }
    eapply mapT_Forall
    with (P := fun e =>
                 exists v,
                   exprD' tus (vars l ++ tvs) e tyProp = Some v) in H.
    generalize H.
    eapply mapT_Forall2'
      with (R :=
              fun e v' =>
                forall v,
                  exprD' tus (vars l ++ tvs) e tyProp = Some v ->
                  forall us vs us',
                    v us vs = v' (hlist_app us us') vs)in H.
    destruct H as [ ? [ ? ? ] ].
    change_rewrite H.
    { eapply conclusionD_weakenU with (tus' := tus') in H0.
      forward_reason.
      Cases.rewrite_all_goal.
      eexists; split; eauto. intros.
      simpl. eapply foralls_iff. intros.
      eapply impls_iff.
      { rewrite Forall2_map2. rewrite Forall2_map1.
        clear H. generalize dependent x. revert H4.
        induction XXX; inversion 2; subst; auto.
        inversion H4; clear H4; subst.
        eapply IHXXX in H9; clear IHXXX; eauto.
        constructor; auto.
        forward_reason.
        generalize H4.
        eapply H7 in H4; clear H7.
        rewrite <- H4; clear H4.
        erewrite H5; clear H5. intros.
        eapply exprD'_weakenU with (tus' := tus') in H4; eauto.
        forward_reason. rewrite H4 in *.
        inv_all; subst. instantiate (1 := us'). rewrite <- H5. reflexivity. }
      { eapply H3. } }
    { simpl. intros.
      destruct H2. generalize H2.
      eapply exprD'_weakenU with (tus' := tus') in H2; eauto.
      destruct H2 as [ ? [ ? ? ] ].
      eexists; split; eauto. intros.
      rewrite H4 in H5. inv_all; subst. auto. }
    { eauto. }
*)
  Admitted.

  Lemma lemmaD'_weakenV
  : forall tus tvs l lD,
      lemmaD' tus tvs l = Some lD ->
      forall tvs',
        exists lD',
          lemmaD' tus (tvs ++ tvs') l = Some lD' /\
          forall us vs vs',
            lD us vs <-> lD' us (hlist_app vs vs').
  Proof.
(*
    (** TODO: This proof is horrible! **)
    unfold lemmaD'; simpl; intros.
    forward.
    inv_all; subst.
    generalize (fun H' =>
                  @mapT_Forall2 _ _
                                 (fun e v =>
                                    exists v',
                                      exprD' tus (vars l ++ tvs ++ tvs') e tyProp = Some v' /\
                                      forall a b c d,
                                        v a (hlist_app b c) = v' a (hlist_app b (hlist_app c d)))
                   _
                   H'
                   _ _ H).
    match goal with
      | |- (?X -> _) -> _ =>
        let H := fresh in
        assert (H : X) ;
          [ | intro XXX; specialize (XXX H) ]
    end.
    { simpl. intros.
      eapply exprD'_weakenV with (tvs' := tvs') in H1;
        eauto with typeclass_instances.
      forward_reason.
      erewrite (@exprD'_conv _ _ _ _ tus tus
                            (vars l ++ tvs ++ tvs')
                            ((vars l ++ tvs) ++ tvs')
                             _ _ eq_refl).
      rewrite H1.
      instantiate (1 := app_ass_trans (vars l) tvs tvs').
      exists match app_ass_trans (vars l) tvs tvs' in _ = tvs'
                   return hlist (typD) tus ->
                          hlist (typD) tvs' -> typD tyProp
             with
               | eq_refl => x0
             end.
      split.
      { clear. revert x0.
        destruct (app_ass_trans (vars l) tvs tvs'). reflexivity. }
      { intros. erewrite H2. instantiate (1 := d).
        rewrite hlist_app_assoc.
        clear.
        match goal with
          | |- _ _ match _ with eq_refl => ?Y end = _ _ ?X =>
            change Y with X; generalize dependent X
        end.
        revert x0.
        destruct (app_ass_trans (vars l) tvs tvs').
        simpl. reflexivity. } }
    eapply mapT_Forall
    with (P := fun e =>
                 exists v,
                   exprD' tus (vars l ++ tvs) e tyProp = Some v) in H.
    generalize H.
    eapply mapT_Forall2'
      with (f := fun e : expr => exprD' tus (vars l ++ tvs ++ tvs') e tyProp)
           (R :=
              fun e v' =>
                forall v,
                  exprD' tus (vars l ++ tvs) e tyProp = Some v ->
                  forall us vs vs' vs'',
                    v us (hlist_app vs vs') = v' us  (hlist_app vs (hlist_app vs' vs''))) in H.
    { destruct H as [ ? [ ? ? ] ].
      rewrite H.
      eapply conclusionD_weakenV with (tvs' := tvs') in H0.
      forward_reason.
      Cases.rewrite_all_goal.
      assert (conclusionD tus (vars l ++ tvs ++ tvs') (concl l) =
              Some match app_ass_trans (vars l) tvs tvs' in _ = tvs
                         return hlist _ tus -> hlist _ tvs -> Prop
                   with
                     | eq_refl => x0
                   end).
      { clear - H0.
        generalize dependent (app_ass_trans (vars l) tvs tvs').
        generalize dependent ((vars l ++ tvs) ++ tvs').
        generalize dependent (vars l ++ tvs ++ tvs').
        intros. subst. assumption. }
      rewrite H4.
      intros.
      eexists; split; eauto. intros.
      simpl. eapply foralls_iff. intros.
      eapply impls_iff.
      { rewrite Forall2_map2. rewrite Forall2_map1.
        clear H. generalize dependent x. revert H5.
        clear H4 conclusionD_weakenU conclusionD_weakenV H0.
        induction XXX; inversion 2; subst; auto.
        clear H8.
        inversion H5; clear H5; subst.
        inversion H2; clear H2; subst.
        constructor; eauto.
        forward_reason.
        generalize H0. eapply H9 in H0; clear H9.
        rewrite <- H0; clear H0.
        erewrite H2; clear H2. instantiate (1 := vs').
        intros. eapply H1 in H0.
        forward_reason. revert H0. Cases.rewrite_all_goal.
        intros; inv_all; subst. reflexivity. }
      { rewrite H3. instantiate (1 := vs').
        rewrite hlist_app_assoc. unfold eq_sym.
        generalize (app_ass_trans (vars l) tvs tvs').
        clear. intros.
        match goal with
          | |- _ _ match _ with eq_refl => ?Y end <-> _ _ ?X =>
            change Y with X; generalize dependent X
        end. revert x0. destruct e. reflexivity. } }
    { simpl. intros.
      destruct H2. generalize H2.
      eapply exprD'_weakenV with (tvs' := tvs') in H2; eauto.
      destruct H2 as [ ? [ ? ? ] ].
      intro. rewrite H4.
      erewrite exprD'_conv with (pfu := eq_refl) (pfv := app_ass_trans (vars l) tvs tvs').
      rewrite H2.
      exists (match
                 app_ass_trans (vars l) tvs tvs' in (_ = tvs'0)
                 return hlist _ tus -> hlist _ tvs'0 -> typD tyProp
               with
                 | eq_refl => x1
               end).
      split.
      { clear. revert x1.
        destruct (app_ass_trans (vars l) tvs tvs'). reflexivity. }
      { intros. inv_all; subst.
        erewrite H3. instantiate (1 := vs'').
        rewrite hlist_app_assoc.
        clear. revert x1.
        generalize dependent (hlist_app vs (hlist_app vs' vs'')).
        destruct (app_ass_trans (vars l) tvs tvs').
        reflexivity. } }
    { eauto. }
*)
  Admitted.

  Lemma lemmaD'_weaken
  : forall tus tvs l lD,
      lemmaD' tus tvs l = Some lD ->
      forall tus' tvs',
        exists lD',
          lemmaD' (tus ++ tus') (tvs ++ tvs') l = Some lD' /\
          forall us us' vs vs',
            lD us vs <-> lD' (hlist_app us us') (hlist_app vs vs').
  Proof.
    clear. intros.
    eapply lemmaD'_weakenU with (tus' := tus') in H.
    destruct H as [ ? [ ? ? ] ].
    eapply lemmaD'_weakenV with (tvs' := tvs') in H.
    destruct H as [ ? [ ? ? ] ].
    eexists; split; eauto.
    intros.
    etransitivity. eapply H0. eapply H1.
  Qed.

  Definition lemmaD (us vs : env) (l : lemma) : Prop :=
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