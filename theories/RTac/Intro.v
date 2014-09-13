Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.Open.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Variable RType_typ : RType typ.
  Variable Expr_expr : Expr RType_typ expr.
  Variable Typ0_Prop : Typ0 _ Prop.
  Variable Subst_subst : Subst subst expr.
  Variable SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst.

(*
  Section at_bottom.
    Variable m : Type -> Type.
    Context {Monad_m : Monad m}.
    Variable gt : list typ -> list typ -> subst -> option expr -> m (Goal typ expr subst).

    Let under (gt : Goal typ expr subst -> Goal typ expr subst)
        (x : m (Goal typ expr subst)) : m (Goal typ expr subst) :=
      bind x (fun x => ret (gt x)).

    Fixpoint at_bottom tus tvs (g : Goal typ expr subst)
    : m (Goal typ expr subst) :=
      match g with
        | GAll x g' => under (GAll x) (at_bottom tus (tvs ++ x :: nil) g')
        | GEx  x g' => under (GEx  x) (at_bottom (tus ++ x :: nil) tvs g')
        | GHyp x g' => under (GHyp x) (at_bottom tus tvs g')
        | GGoal s e => gt tus tvs s e
      end.
  End at_bottom.
*)

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
          More sub (GAll t (GGoal sub (g' (Var nv))))
        | Some (AsEx t g') =>
          let nu := countUVars ctx in
          More sub (GEx t (GGoal sub (g' (UVar nu))))
        | Some (AsHy h g') =>
          More sub (GHyp h (GGoal sub g'))
      end.

(*
  Definition open_sound (open : expr -> option ((typ + expr) * expr)) : Prop :=
    forall tus tvs e eD h e',
      open e = Some (h,e') ->
      propD tus tvs e = Some eD ->
      match h with
        | inl t =>
          exists eD',
          propD tus (t :: tvs) e' = Some eD' /\
          forall us vs,
            (eD us vs) -> (forall x : typD t, eD' us (HList.Hcons x vs))
        | inr h =>
          False
      end.
*)

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

(*
  Theorem INTRO_sound
  : forall open, open_sound open ->
                 rtac_sound nil nil (INTRO open).
  Proof.
    unfold rtac_sound, INTRO.
    intros.
    eapply at_bottom_sound_option in H0; eauto.
(*
    { destruct (goalD nil nil g); destruct (goalD nil nil g'); auto.
*)
  Abort.
*)
*)

End parameterized.
