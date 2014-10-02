Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.RTac.Core.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Subst_subst : Subst subst expr}.
  Context {SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst}.

  Context {ExprOk_expr : ExprOk Expr_expr}.

  Variable substV : (nat -> option expr) -> expr -> expr.
  Variable Var : nat -> expr.
  Variable UVar : nat -> expr.

  Inductive OpenAs :=
  | AsEx : typ -> (expr -> expr) -> OpenAs
  | AsAl : typ -> (expr -> expr) -> OpenAs
  | AsHy : expr -> expr -> OpenAs.

  Variable open : expr -> option OpenAs.

  Definition INTRO
  : rtac typ expr subst :=
    fun ctx sub gl =>
      match open gl with
        | None => Fail
        | Some (AsAl t g') =>
          let nv := countVars ctx in
          More sub (GAll t (GGoal (g' (Var nv))))
        | Some (AsEx t g') =>
          let nu := countUVars ctx in
          More sub (GEx t None (GGoal (g' (UVar nu))))
        | Some (AsHy h g') =>
          More sub (GHyp h (GGoal g'))
      end.

  Definition open_sound : Prop :=
    forall tus tvs e ot,
      open e = Some ot ->
      match ot with
        | AsAl t gl' =>
          forall eD e' e'D,
            propD tus tvs e = Some eD ->
            exprD' tus (tvs ++ t :: nil) e' t = Some e'D ->
            exists eD',
              propD tus (tvs ++ t :: nil) (gl' e') = Some eD' /\
              forall us vs,
                (forall x : typD t,
                   eD' us (hlist_app vs (Hcons (e'D us (hlist_app vs (Hcons x Hnil))) Hnil))) ->
                (eD us vs)
        | AsEx t gl' =>
          forall eD e' e'D,
            propD tus tvs e = Some eD ->
            exprD' (tus ++ t :: nil) tvs e' t = Some e'D ->
            exists eD',
              propD (tus ++ t :: nil) tvs (gl' e') = Some eD' /\
              forall us vs,
                (exists x : typD t,
                   eD' (hlist_app us (Hcons (e'D (hlist_app us (Hcons x Hnil)) vs) Hnil)) vs) ->
                (eD us vs)
        | AsHy h gl' =>
          forall eD,
            propD tus tvs e = Some eD ->
            exists eD' hD,
              propD tus tvs h = Some hD /\
              propD tus tvs gl' = Some eD' /\
              forall us vs,
                (hD us vs -> eD' us vs) ->
                (eD us vs)
      end.

  Hypothesis Hopen : open_sound.

  Theorem INTRO_sound : rtac_sound nil nil INTRO.
  Proof.
    unfold rtac_sound, INTRO.
    intros; subst.
    red in Hopen.
    specialize (@Hopen (getUVars ctx nil) (getVars ctx nil) g).
    destruct (open g); auto.
    specialize (Hopen _ eq_refl).
    destruct o; intros; split; auto.
    { simpl. forward.
      eapply exprD'_typ0_weakenU with (tus' := t :: nil) in H0; eauto.
      forward_reason.
      unfold exprD'_typ0 in H0.
      autorewrite with eq_rw in H0; forwardy.
      assert (exists eD',
                exprD' (getUVars ctx nil ++ t :: nil) (getVars ctx nil)
                       (UVar (countUVars ctx)) t = Some eD' /\
                forall us vs x,
                  eD' (hlist_app us (Hcons x Hnil)) vs = x).
      { admit. }
      forward_reason.
      specialize (@Hopen _ (UVar (countUVars ctx)) _ eq_refl H4).
      inv_all; subst.
      destruct Hopen as [ ? [ ? ? ] ].
      rewrite H3.
      admit. }
    { simpl. forward.
      eapply exprD'_typ0_weakenV with (tvs' := t :: nil) in H0; eauto.
      (** Same proof as above **)
      admit. }
    { simpl; forward.
      specialize (Hopen _ eq_refl).
      destruct Hopen as [ ? [ ? [ ? [ ? ? ] ] ] ]; clear Hopen.
      rewrite H2.
      rewrite H3.
      simpl.
      eapply ctxD'_no_hyps.
      intros. split; auto. }
  Qed.

End parameterized.


(*
  Lemma _impls_sem
  : forall ls P,
      _impls ls P <-> (Forall (fun x => x) ls -> P).
  Proof.
    induction ls; simpl; intros.
    + intuition.
    + rewrite IHls. intuition.
      inversion H0. eapply H; eauto.
  Qed.
  Lemma _exists_iff
  : forall ls P Q,
      (forall x, P x <-> Q x) ->
      (@_exists ls P <-> @_exists ls Q).
  Proof.
    clear.
    induction ls; simpl; intros.
    + eapply H.
    + apply exists_iff; intro. eapply IHls.
      intro; eapply H.
  Qed.
  Lemma _forall_iff
  : forall ls P Q,
      (forall x, P x <-> Q x) ->
      (@_foralls ls P <-> @_foralls ls Q).
  Proof.
    clear.
    induction ls; simpl; intros.
    + eapply H.
    + apply forall_iff; intro. eapply IHls.
      intro; eapply H.
  Qed.

  Lemma at_bottom_sound_option
  : forall goal tus tvs f goal',
      (forall tus' tvs' s e e',
         f (tus ++ tus') (tvs ++ tvs') s e = Some e' ->
         WellFormed_subst s ->
         match goalD (tus ++ tus') (tvs ++ tvs') (GGoal s e)
             , goalD (tus ++ tus') (tvs ++ tvs') e'
         with
           | None , _ => True
           | Some _ , None => False
           | Some g , Some g' =>
             forall us vs,
               g' us vs -> g us vs
         end) ->
      at_bottom f tus tvs goal = Some goal' ->
      forall (Hwf : WellFormed_goal goal),
      match goalD tus tvs goal
          , goalD tus tvs goal'
      with
        | None , _ => True
        | Some _ , None => False
        | Some g , Some g' =>
          forall us vs,
            g' us vs -> g us vs
      end.
  Proof.
    induction goal; simpl; intros.
    { forwardy. inv_all; subst.
      eapply IHgoal in H0; clear IHgoal; auto.
      { simpl. forward. auto. }
      { intros.
        specialize (H tus' (t :: tvs') s e).
        rewrite app_ass in H1. simpl in *.
        eapply H in H1; clear H; auto.
        forward.
        rewrite substD_conv
           with (pfu := eq_refl _) (pfv := eq_sym (HList.app_ass_trans _ _ _)) in H.
        unfold propD in *.
        rewrite exprD'_typ0_conv with (pfu := eq_refl _)
             (pfv := eq_sym (HList.app_ass_trans _ _ _)) in H.
        simpl in *.
        unfold ResType in *.
        autorewrite with eq_rw in *.
        destruct e; forwardy.
        { inv_all; subst.
          rewrite H in *.
          autorewrite with eq_rw in H3.
          forwardy.
          rewrite H3 in *.
          inv_all; subst.
          rewrite goalD_conv with (pfu := eq_refl)
                                  (pfv := eq_sym (HList.app_ass_trans _ _ _)).
          simpl.
          forwardy.
          autorewrite with eq_rw.
          rewrite H1.
          intros us vs. autorewrite with eq_rw.
          clear - H4.
          match goal with
            | |- _ _ match ?X with _ => _ end ->
                 _ _ match ?Y with _ => _ end /\
                 _ _ match ?Z with _ => _ end =>
              change X with Y ; change Z with Y ; destruct Y
          end.
          eauto. }
        { rewrite H in *.
          rewrite goalD_conv with (pfu := eq_refl)
                                  (pfv := eq_sym (HList.app_ass_trans _ _ _)).
          simpl.
          forwardy.
          autorewrite with eq_rw.
          rewrite H1. intros.
          inv_all; subst.
          revert H6.
          match goal with
            | |- match ?X with _ => _ end _ _ ->
                 match ?Y with _ => _ end _ _ =>
              change Y with X ; destruct X
          end. auto. } } }
    { forwardy; inv_all; subst.
      eapply IHgoal in H0; clear IHgoal; auto.
      + simpl; forward; eauto.
        destruct H3. eauto.
      + intros.
        rewrite goalD_conv
           with (pfu := eq_sym (HList.app_ass_trans _ _ _))
                (pfv := eq_refl).
        autorewrite with eq_rw.
        simpl. forward.
        rewrite HList.app_ass_trans in H1.
        simpl in H1.
        eapply H in H1; clear H; eauto.
        destruct e; forward.
        - inv_all; subst.
          revert H7. autorewrite with eq_rw.
          eauto.
        - inv_all; subst.
          revert H6. autorewrite with eq_rw.
          eauto. }
    { forwardy; inv_all; subst.
      eapply IHgoal in H0; clear IHgoal; eauto.
      + simpl; forward; eauto.
        inv_all. subst.
        eapply _impls_sem; intro.
        eapply _impls_sem in H5; eauto. }
    { specialize (H nil nil s o goal').
      simpl in H.
      repeat rewrite HList.app_nil_r_trans in H.
      eapply H in H0; clear H; auto. }
  Qed.
*)
