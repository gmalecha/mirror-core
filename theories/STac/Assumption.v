Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.ListMapT.
Require Import MirrorCore.LemmaApply.
Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.STac.Core.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.
  Context {RType_typ : RType typ}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Let tyProp : typ := @typ0 _ _ _ _.

  Variable exprUnify : tenv typ -> tenv typ -> nat -> expr -> expr -> typ -> subst -> option subst.

  Fixpoint find_assumption (tus tvs : tenv typ) (goal : expr)
           (hs : list expr) (s : subst)
  : option subst :=
    match hs with
      | nil => None
      | h :: hs =>
        match exprUnify tus tvs 0 h goal tyProp s with
          | None => find_assumption tus tvs goal hs s
          | Some s => Some s
        end
    end.

  Section assumption.
    Context {Subst_subst : Subst subst expr}.
    Context {SU : SubstUpdate subst expr}.


    (** Think of this like:
     **   apply lem ; cont
     ** i.e. first apply the lemma and then require that all side-conditions
     ** except the last are solved by the prover [tac], currently with
     ** empty facts.
     **)
    Definition ASSUMPTION : stac typ expr subst :=
      fun tus tvs sub hs e =>
        match find_assumption tus tvs e hs sub with
          | None => Fail
          | Some sub' =>
            Solved nil nil sub'
        end.
  End assumption.

  Context {Expr_expr : Expr RType_typ expr}.
  Context {Subst_subst : Subst subst expr}.
  Context {SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst}.
  Context {UnifySound_exprUnify : unify_sound exprUnify}.

  Lemma find_assumption_sound
  : forall tus tvs needle haystack sub sub',
      find_assumption tus tvs needle haystack sub = Some sub' ->
      WellFormed_subst sub ->
      WellFormed_subst sub' /\
      match stateD tus tvs sub haystack needle with
        | Some P =>
          match substD tus tvs sub' with
            | Some sV' =>
              forall us vs,
                sV' us vs -> P us vs
            | None => False
          end
        | None => True
      end.
  Proof.
    Opaque mapT.
    induction haystack; simpl; try congruence; intros.
    match goal with
      | H : match ?X with _ => _ end = _ |- _ =>
        consider X; intros
    end.
    { inv_all; subst.
      red in UnifySound_exprUnify.
      eapply UnifySound_exprUnify with (tv' := nil) in H; eauto.
      forward_reason; split; auto.
      unfold stateD. simpl in *.
      rewrite list_mapT_cons.
      forward; inv_all; subst.
      unfold propD, ExprDAs.exprD'_typ0 in H2, H3.
      forwardy; inv_all; subst.
      match goal with
        | H : _ , H' : _ , H'' : _ |- _ =>
          specialize (H _ _ _ H' H'' eq_refl)
      end.
      forward_reason.
      Cases.rewrite_all_goal.
      intros. inversion H8; clear H8; subst.
      eapply H5 in H7; clear H5.
      forward_reason; split; auto.
      revert H11.
      autorewrite with eq_rw.
      specialize (H7 Hnil); simpl in H7.
      rewrite H7. exact (fun x => x). }
    { clear H. eapply IHhaystack in H1; eauto.
      forward_reason; split; auto.
      unfold stateD in *.
      rewrite list_mapT_cons.
      forward; inv_all; subst.
      intros. eapply H8; auto.
      inversion H5; assumption. }
  Qed.

  Theorem ASSUMPTION_sound
  : stac_sound ASSUMPTION.
  Proof.
    unfold stac_sound, ASSUMPTION; intros.
    consider (find_assumption tus tvs g hs s).
    { intros. eapply find_assumption_sound in H0; eauto.
      intuition.
      forward.
      rewrite substD_conv
         with (pfu := eq_sym (HList.app_nil_r_trans tus))
              (pfv := eq_sym (HList.app_nil_r_trans tvs)).
      rewrite H2.
      autorewrite with eq_rw.
      intros. apply H3.
      forward_reason.
      specialize (H4 HList.Hnil).
      rewrite HList.hlist_app_nil_r in H4.
      revert H4. clear.
      rewrite (HList.hlist_eta x).
      rewrite HList.hlist_app_nil_r.
      destruct (eq_sym (app_nil_r_trans tus)).
      destruct (eq_sym (app_nil_r_trans tvs)).
      exact (fun x => x). }
    { trivial. }
  Qed.

End parameterized.

Arguments ASSUMPTION {_ _ _ _ _} _ _ _ _ _ _.