Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Lambda2.TypesI2.
Require Import MirrorCore.Lambda2.ExprCore.
Require Import MirrorCore.Lambda2.ExprDIm.

Set Implicit Arguments.
Set Strict Implicit.

Module Make (ED : ExprDenote)
<: ExprFacts ED.

  Create HintDb exprD_rw discriminated.

  Hint Rewrite @ED.exprD'_Abs @ED.exprD'_App @ED.exprD'_Var : exprD_rw.
  Hint Rewrite @ED.exprD'_UVar @ED.exprD'_Inj : exprD_rw.
  Hint Rewrite ED.arr_match_typ_arr : exprD_rw.
  Hint Rewrite ED.type_cast_refl : exprD_rw.

  Lemma type_cast_non_Rty : forall a b, ~ED.Rty a b -> ED.type_cast a b = None.
  Proof.
    intros. consider (ED.type_cast a b); auto.
    intros. exfalso. auto.
  Qed.

  Lemma type_cast_Rty : forall a b (pf : ED.Rty a b),
                          ED.type_cast a b = Some pf.
  Proof.
    intros. red in pf.  subst. apply ED.type_cast_refl.
  Qed.

  Hint Rewrite type_cast_Rty type_cast_non_Rty using solve [ auto ] : exprD_rw.

  Ltac red_exprD :=
    autorewrite with exprD_rw in *.

  Section over_func.
    Variable func : Type.
    Variable RSym_func : RSym (fun _ => ED.typD) func.

    Lemma typeof_expr_weaken
    : forall tus tvs e t tus' tvs',
        ED.typeof_expr tus tvs e = Some t ->
        ED.typeof_expr (tus ++ tus') (tvs ++ tvs') e = Some t.
    Proof.
      intros tus tvs e; revert tvs.
      induction e; simpl; intros; auto using ListNth.nth_error_weaken.
      { forward. Cases.rewrite_all_goal. auto. }
      { forward. eapply IHe in H. simpl in H. rewrite H. auto. }
    Qed.

    Theorem exprD'_weaken
    : forall tus tvs e t val tus' tvs',
        ED.exprD' tus tvs t e = Some val ->
        exists val',
          ED.exprD' (tus ++ tus') (tvs ++ tvs') t e = Some val' /\
          forall us vs us' vs',
            val us vs = val' (hlist_app us us') (hlist_app vs vs').
    Proof.
      intros tus tvs e; revert tvs.
      induction e; intros; red_exprD; simpl in *.
      { forward; inv_all; subst.
        eapply nth_error_get_hlist_nth_weaken in H0.
        destruct H0 as [ ? [ ? ? ] ].
        rewrite H. simpl. rewrite H1.
        eexists; split; eauto.
        simpl in *. intros.
        unfold ED.Rcast_val. rewrite <- H0. reflexivity. }
      { forward. inv_all; subst. eexists; split; eauto. }
      { forward; inv_all; subst.
        eapply typeof_expr_weaken in H.
        rewrite H.
        eapply IHe1 in H0. destruct H0 as [ ? [ ? ? ] ].
        rewrite H0.
        eapply IHe2 in H1. destruct H1 as [ ? [ ? ? ] ].
        rewrite H1. eexists; split; eauto.
        unfold ED.Open_App.
        intros.
        repeat (rewrite eq_Arr_eq; rewrite eq_Const_eq).
        rewrite <- H3.
        match goal with
          | |- match ?X with _ => _ end _ _ _ = _ =>
            generalize X
        end.
        clear - H2.
        generalize dependent (ED.typD (ED.typ_arr t0 t)).
        intros; subst. rewrite <- H2. reflexivity. }
      { destruct (ED.arr_match_case t0).
        { destruct H0 as [ ? [ ? [ ? ? ] ] ].
          rewrite H0 in *; clear H0.
          red in x1. subst. simpl in *.
          repeat first [ rewrite eq_option_eq in *
                       | rewrite eq_Arr_eq in *
                       | rewrite eq_Const_eq in * ].
          forward; inv_all; subst.
          eapply IHe in H1.
          destruct H1 as [ ? [ ? ? ] ].
          simpl in H0. rewrite H0.
          eexists; split; eauto.
          intros.
          unfold ED.OpenT.
          repeat first [ rewrite eq_option_eq in *
                       | rewrite eq_Arr_eq in *
                       | rewrite eq_Const_eq in * ].
          revert H1. clear. simpl in *.
          destruct (eq_sym (ED.typD_arr x x0)).
          intros. eapply FunctionalExtensionality.functional_extensionality.
          intros. specialize (H1 us (Hcons (ED.Rcast_val r x2) vs)).
          simpl in *. auto. }
        { rewrite H0 in H. congruence. } }
      { forward; inv_all; subst.
        eapply nth_error_get_hlist_nth_weaken in H0.
        destruct H0 as [ ? [ ? ? ] ].
        rewrite H. simpl. rewrite H1.
        eexists; split; eauto.
        simpl in *. intros.
        rewrite <- H0. reflexivity. }
    Qed.

    Theorem exprD'_type_cast
    : forall tus tvs e t,
        ED.exprD' tus tvs t e =
        match ED.typeof_expr tus tvs e with
          | None => None
          | Some t' =>
            match ED.type_cast t' t with
              | None => None
              | Some cast =>
                match ED.exprD' tus tvs t' e with
                  | None => None
                  | Some x =>
                    Some (fun us gs => ED.Rcast (fun x => x) cast (x us gs))
                end
            end
        end.
    Proof.
    Admitted.

    Theorem typeof_expr_exprD'
    : forall tus tvs e t,
        ED.typeof_expr tus tvs e = Some t ->
        exists val,
          ED.exprD' tus tvs t e = Some val.
    Proof.
    Admitted.
  End over_func.

End Make.