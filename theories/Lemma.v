Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.Compat.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.Util.ListMapT.

Set Implicit Arguments.
Set Strict Implicit.
Set Primitive Projections.

Section lem.
  Variable typ : Set.
  Variable expr : Set.
  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr _ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.
  Variable conclusion : Set.

  Record lemma : Set := mkLemma
  { vars : list typ
  ; premises : list expr
  ; concl : conclusion
  }.

  Variable conclusionD : forall us vs, conclusion -> option (exprT us vs Prop).

  Context {Typ0_Prop : Typ0 _ Prop}.

  Fixpoint foralls (ls : list typ) : (OpenT typD ls Prop) -> Prop :=
    match ls as ls return (OpenT typD ls Prop) -> Prop with
      | nil => fun P => P Hnil
      | l :: ls => fun P => foralls (fun z => forall x : typD l, P (Hcons x z))
    end.

  Lemma foralls_sem : forall ls P,
    foralls (ls := ls) P <-> forall h, P h.
  Proof.
    clear.
    induction ls; simpl; intros.
    { intuition; rewrite hlist_eta; auto. }
    { intuition.
      { rewrite hlist_eta.
        eapply IHls in H. eapply H. }
      { eapply IHls. eauto. } }
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
                         (fun e : expr => exprD_typ0 tus (vars l ++ tvs) e)
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

  Hypothesis conclusionD_weaken
  : forall tus tvs l lD,
      conclusionD tus tvs l = Some lD ->
      forall tus' tvs',
        exists lD',
          conclusionD (tus ++ tus') (tvs ++ tvs') l = Some lD' /\
          forall us us' vs vs',
            lD us vs <-> lD' (hlist_app us us') (hlist_app vs vs').

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

  Set Printing Universes.

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
    forward.
    inv_all; subst.
    generalize (fun H' =>
                  @mapT_Forall2 _ _
                                 (fun e v =>
                                    exists v',
                                      exprD_typ0 (tus ++ tus') (vars l ++ tvs ++ tvs') e = Some v' /\
                                      forall a b c d e,
                                        v a (hlist_app b c) = v' (hlist_app a e) (hlist_app b (hlist_app c d)))
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
      eapply (exprD_typ0_weaken tus' tvs') in H1;
        eauto with typeclass_instances.
      forward_reason.
      rewrite exprD_typ0_conv with (pfu := eq_refl)
                                    (pfv := eq_sym (app_ass_trans@{Set} (vars l) tvs tvs')) in H1.
      autorewrite_with_eq_rw_in H1. forward.
      inv_all; subst.
      eexists; split; eauto.
      intros. specialize (H2 a0 (hlist_app b c) e1 d).
      rewrite H2.
      autorewrite with eq_rw.
      rewrite hlist_app_assoc.
      generalize (app_ass_trans (vars l) tvs tvs').
      generalize (hlist_app b (hlist_app c d)).
      clear. destruct e. reflexivity. }
    eapply mapT_Forall
    with (P := fun e =>
                 exists v,
                   exprD_typ0 (tus ++ tus') (vars l ++ tvs ++ tvs') e = Some v) in H.
    { eapply mapT_Forall2'
      with (f := fun e : expr => exprD_typ0 (tus ++ tus') (vars l ++ tvs ++ tvs') e)
           (ls := l.(premises))
           (R :=
              fun e (v' : exprT (tus ++ tus') (vars l ++ tvs ++ tvs') Prop) =>
                forall v : exprT tus (vars l ++ tvs) Prop,
                  exprD_typ0 tus (vars l ++ tvs) e = Some v ->
                  forall us us' vs vs' vs'',
                    v us (hlist_app vs vs') = v' (hlist_app us us')  (hlist_app vs (hlist_app vs' vs''))) in H.
    { destruct H as [ ? [ ? ? ] ].
      rewrite H.
      eapply conclusionD_weaken with (tus' := tus') (tvs' := tvs') in H0.
      forward_reason.
      Cases.rewrite_all_goal.
      assert (conclusionD (tus ++ tus') (vars l ++ tvs ++ tvs') (concl l) =
              Some match app_ass_trans (vars l) tvs tvs' in _ = tvs
                         return hlist _ (tus ++ tus') -> hlist _ tvs -> Prop
                   with
                     | eq_refl => x0
                   end).
      { clear - H0.
        generalize dependent (app_ass_trans@{Set} (vars l) tvs tvs').
        generalize dependent ((vars l ++ tvs) ++ tvs').
        generalize dependent (vars l ++ tvs ++ tvs').
        intros. subst. assumption. }
      rewrite H4.
      intros.
      eexists; split; eauto. intros.
      simpl. eapply foralls_iff. intros.
      eapply impls_iff.
      { rewrite Forall2_map2. rewrite Forall2_map1.
        generalize dependent x.
        clear H4 conclusionD_weaken.
        induction XXX.
        { inversion 2; subst; auto. }
        { intros.
          inversion H4; clear H4; subst.
          rewrite list_mapT_cons in H2.
          destruct H as [ ? [ ? ? ] ].
          rewrite H in H2.
          forward. inv_all. subst.
          specialize (IHXXX _ eq_refl H9).
          constructor; eauto.
          { rewrite <- H4. reflexivity. } } }
      { autorewrite with eq_rw.
        rewrite H3.
        rewrite (hlist_app_assoc@{Set Urefl} x1 vs vs').
        reflexivity. } }
    { intros. destruct H2.
      rewrite H2. eexists; split; eauto.
      intros.
      eapply (exprD_typ0_weaken tus' tvs') in H3.
      destruct H3 as [ ? [ ? ? ] ].
      rewrite H4 with (us' := us') (vs' := vs''); clear H4.
      rewrite hlist_app_assoc.
      rewrite exprD_typ0_conv with (pfu := eq_refl) (pfv := app_ass_trans _ _ _) in H2.
      autorewrite_with_eq_rw_in H2.
      rewrite H3 in *. inv_all; subst.
      autorewrite with eq_rw.
      reflexivity. } }
    { intros.
      eapply (exprD_typ0_weaken tus' tvs') in H2.
      destruct H2 as [ ? [ ? ? ] ].
      rewrite exprD_typ0_conv with (pfu := eq_refl)
                                      (pfv := eq_sym (app_ass_trans _ _ _)) in H2.
      autorewrite_with_eq_rw_in H2.
      forward. eauto. }
  Qed.

  Lemma lemmaD'_conv
  : forall tus tvs tus' tvs' (pfu : tus' = tus) (pfv : tvs' = tvs),
      lemmaD' tus tvs =
      match pfu in _ = X , pfv in _ = Y return _ -> option (exprT X Y Prop) with
        | eq_refl , eq_refl => lemmaD' tus' tvs'
      end.
  Proof. destruct pfu; destruct pfv; reflexivity. Qed.

  Lemma lemmaD'_weakenU
  : forall tus tvs l lD,
      lemmaD' tus tvs l = Some lD ->
      forall tus',
        exists lD',
          lemmaD' (tus ++ tus') tvs l = Some lD' /\
          forall us us' vs,
            lD us vs <-> lD' (hlist_app us us') vs.
  Proof.
    intros.
    eapply lemmaD'_weaken with (tus' := tus') (tvs' := nil) in H.
    destruct H as [ ? [ ? ? ] ].
    rewrite lemmaD'_conv with (pfu := eq_refl) (pfv := app_nil_r_trans tvs).
    autorewrite_with_eq_rw.
    rewrite H. eexists; split; eauto.
    intros.
    etransitivity.
    eapply H0 with (us' := us') (vs' := Hnil).
    rewrite hlist_app_nil_r.
    autorewrite with eq_rw.
    reflexivity.
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
    eapply lemmaD'_weaken with (tvs' := tvs') (tus' := nil) in H.
    destruct H as [ ? [ ? ? ] ].
    rewrite lemmaD'_conv with (pfv := eq_refl) (pfu := app_nil_r_trans tus).
    autorewrite_with_eq_rw.
    rewrite H. eexists; split; eauto.
    intros.
    etransitivity.
    eapply H0 with (vs' := vs') (us' := Hnil).
    rewrite hlist_app_nil_r.
    autorewrite with eq_rw.
    reflexivity.
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

  Lemma lemmaD_lemmaD' : forall (l : lemma),
      lemmaD nil nil l <->
      exists pf, lemmaD' nil nil l = Some pf /\
                 pf Hnil Hnil.
  Proof using.
    clear. unfold lemmaD. simpl. intros.
    destruct (lemmaD' nil nil l).
    { split; eauto. intros; forward_reason.
      inv_all. subst. assumption. }
    { split; intros. inversion H. forward_reason. inversion H. }
  Qed.

End lem.

Require Import MirrorCore.Reify.ReifyClass.

Section rlemma_tc.
  Context {ty pr c : Set}.
  Context {rT : Reify ty}.
  Context {rU : Reify pr}.
  Context {rV : Reify c}.

  Definition tc_lemma (ignores : list RPattern) : Set :=
    lemma ty pr c.

  Variable ignores : list RPattern.

  Definition add_var (v : ty) (x : lemma ty pr c) : lemma ty pr c :=
    {| vars := vars x ++ v :: nil
     ; premises := premises x
     ; concl := concl x |}.

  Definition add_prem (v : pr) (x : lemma ty pr c) : lemma ty pr c :=
    {| vars := vars x
     ; premises := v :: premises x
     ; concl := concl x |}.


  Definition reify_tc_lemma : Command@{Set} (tc_lemma ignores) :=
    Eval unfold CPattern in
    CFix
      (CFirst (   (** Reify type classes, note each one is ignored *)
                  map (fun p =>
                         CPattern (ls:=(tc_lemma ignores : Type)::nil)
                           (RPi p (RGet 0 RIgnore))
                           (fun (y : function (CRec 0)) => y))
                      ignores
               ++ (** Reifies premises *)
                  CPattern (ls:=(pr : Type)::(tc_lemma ignores : Type)::nil)
                           (RImpl (RGet 0 RIgnore) (RGet 1 RIgnore))
                           (fun (x : function (CCall (reify_scheme _)))
                              (y : function (CRec 0)) => add_prem x y)
               :: CPattern (ls:=(ty : Type)::(tc_lemma ignores : Type)::nil)
                           (RPi (RGet 0 RIgnore) (RGet 1 RIgnore))
                           (fun (x : function (CCall (reify_scheme _)))
                              (y : function (CRec 0)) => add_var x y)
               :: CMap (fun x => {| vars := nil
                               ; premises := nil
                               ; concl := x |}) (reify_scheme _)
               :: nil)).

  Global Instance Reify_tc_lemma : Reify (tc_lemma ignores) :=
  { reify_scheme := CCall reify_tc_lemma }.

End rlemma_tc.

Arguments tc_lemma ty pr c ignores : clear implicits, rename.

Typeclasses Opaque tc_lemma.

Section rlemma.
  Context {ty pr c : Set}.
  Context {rT : Reify ty}.
  Context {rU : Reify pr}.
  Context {rV : Reify c}.

  Definition reify_lemma : Command@{Set} (lemma ty pr c) :=
    reify_tc_lemma nil.

  Global Instance Reify_rlemma : Reify (lemma ty pr c) :=
  { reify_scheme := CCall reify_lemma }.

End rlemma.
