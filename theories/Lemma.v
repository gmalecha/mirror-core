Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.ListMapT.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.

Set Implicit Arguments.
Set Strict Implicit.

Section lem.
  Variable typ : Type.
  Variable RType_typ : RType typ.
  Variable expr : tenv typ -> tenv typ -> typ -> Type.
  Variable Expr_expr : Expr _ expr.
  Hypothesis ExprOk_expr : ExprOk Expr_expr.
  Variable conclusion : tenv typ -> tenv typ -> Type.
  Variable conclusionD : forall us vs, conclusion us vs -> ResType us vs Prop.

  Context {tyProp : typ}.
  Variable Provable' : typD nil tyProp -> Prop.

  Record lemma tus tvs : Type := Build_lemma
  { vars : list typ
  ; premises : list (expr tus (vars ++ tvs) tyProp)
  ; concl : conclusion tus (vars ++ tvs)
  }.

  Fixpoint foralls (ls : list typ) : (hlist (typD nil) ls -> Prop) -> Prop :=
    match ls as ls return (hlist (typD nil) ls -> Prop) -> Prop with
      | nil => fun P => P Hnil
      | l :: ls => fun P => forall x : typD nil l,
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


  Definition lemmaD' (tus tvs : tenv typ) (l : lemma tus tvs)
  : ResType tus tvs Prop :=
    match
        Traversable.mapT (T := list) (F := option)
                         (fun e : expr _ _ tyProp => exprD' tus (vars l ++ tvs) tyProp e)
                         (premises l)
      , conclusionD (concl l)
    with
      | Some prems , Some concl =>
        Some (fun us vs =>
                foralls (fun h : hlist (typD nil) (vars l) =>
                           let vs' := hlist_app h vs in
                           impls (map (fun x => Provable' (x us vs')) prems)
                                 (concl us vs')))
      | _ , _ => None
    end.

  Variable concl_weaken : forall tus tvs tus' tvs', conclusion tus tvs -> conclusion (tus ++ tus') (tvs ++ tvs').
  Variable concl_conv : forall tus tvs tus' tvs', (unit -> tus = tus') -> (unit -> tvs = tvs') ->
                                                  conclusion tus tvs -> conclusion tus' tvs'.
  Hypothesis concl_weaken_sound
  : forall tus tvs tus' tvs' (c : conclusion tus tvs) cD,
      conclusionD c = Some cD ->
      exists cD',
        conclusionD (@concl_weaken tus tvs tus' tvs' c) = Some cD' /\
        forall us vs us' vs',
          cD us vs <-> cD' (HList.hlist_app us us') (hlist_app vs vs').

(*
  Hypothesis conclusionD_weakenU
  : forall tus tvs (l : conclusion tus tvs) lD,
      conclusionD l = Some lD ->
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
*)

  Opaque Traversable.mapT.

  Definition lemma_weaken (tus tvs tus' tvs' : tenv typ) (l : lemma tus tvs)
  : lemma (tus ++ tus') (tvs ++ tvs') :=
    @Build_lemma (tus ++ tus') (tvs ++ tvs')
                 l.(vars)
                 (map (fun e =>
                         conv (fun _ => eq_refl) (fun _ => app_ass_trans l.(vars) tvs tvs')
                              (weaken tus' tvs' e))
                      l.(premises))
                 (concl_conv (fun _ => eq_refl) (fun _ => app_ass_trans l.(vars) tvs tvs')
                             (concl_weaken tus' tvs' l.(concl))).

  Lemma lemmaD'_weaken
  : forall tus tvs (l : lemma tus tvs) lD,
      lemmaD' l = Some lD ->
      forall tus' tvs',
        exists lD',
          lemmaD' (lemma_weaken tus' tvs' l) = Some lD' /\
          forall us us' vs vs',
            lD us vs <-> lD' (hlist_app us us') (hlist_app vs vs').
  Proof.
    clear. intros.
(*
    eapply lemmaD'_weakenU with (tus' := tus') in H.
    destruct H as [ ? [ ? ? ] ].
    eapply lemmaD'_weakenV with (tvs' := tvs') in H.
    destruct H as [ ? [ ? ? ] ].
    eexists; split; eauto.
    intros.
    etransitivity. eapply H0. eapply H1.
  Qed.
*)
  Admitted.

End lem.