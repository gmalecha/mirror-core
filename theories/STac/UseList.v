Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.ListMapT.
Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.STac.Core.
Require Import MirrorCore.STac.Continuation.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.
  Variable RType_typ : RType typ.
  Variable Typ0_Prop : Typ0 _ Prop.
  Let tyProp : typ := @typ0 _ _ _ _.

  Variable Expr_expr : Expr RType_typ expr.
  Variable ExprOk_expr : ExprOk Expr_expr.
  Variable Subst_subst : Subst subst expr.
  Variable SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst.
  Variable SubstUpdate_subst : SubstUpdate subst expr.
  Variable SubstUpdateOk_subst : SubstUpdateOk SubstUpdate_subst SubstOk_subst.

  Section use_list.
    Variables (tus tvs : list typ) (hs : list expr).

    Fixpoint use_list' (tacs : list (stac typ expr subst))
             (sub : subst) (es : list expr)
             {struct es}
    : Result typ expr subst :=
      match es , tacs with
        | nil , nil => @Solved _ _ _ nil nil sub
        | e :: es , tac :: tacs =>
          match tac tus tvs sub hs e with
            | Solved nil nil sub' =>
              use_list' tacs sub' es
            | More tus tvs sub hs e =>
              match es with
                | nil => More tus tvs sub hs e
                | _ => (** TODO: This could be more liberal **)
                  @Fail _ _ _
              end
            | _ => @Fail _ _ _
          end
        | _ , _ => @Fail _ _ _
      end.

  End use_list.

  Definition use_list (tacs : list (stac typ expr subst))
  : stac_cont typ expr subst :=
    fun tus tvs sub hs es =>
      use_list' tus tvs hs tacs sub es.

  Theorem use_list_sound
  : forall tacs, Forall stac_sound tacs ->
                stac_cont_sound (use_list tacs).
  Proof.
    Opaque mapT.
    red.
    intros tacs Htacs tus tvs sub hyps gs; revert sub; revert Htacs; revert tacs.
    induction gs; destruct 1; simpl; intros; auto.
    { split; auto.
      forward.
      erewrite substD_conv with (pfv := eq_sym (app_nil_r_trans tvs))
                                (pfu := eq_sym (app_nil_r_trans tus)).
      rewrite H2.
      repeat rewrite eq_option_eq.
      intros. forward_reason.
      rewrite (hlist_eta x) in *; clear x.
      specialize (H3 Hnil).
      do 2 rewrite hlist_app_nil_r in H3.
      destruct (eq_sym (app_nil_r_trans tvs)).
      destruct (eq_sym (app_nil_r_trans tus)).
      intuition.
      rewrite list_mapT_nil in H1.
      inv_all; subst. constructor. }
    { rename H into Htac.
      rename H0 into H.
      consider (x tus tvs sub hyps a); auto; intros.
      { eapply stac_sound_Solved in H0; eauto.
        forward_reason.
        unfold stateD in *.
        forward. subst.
        consider (use_list l tus tvs s hyps gs); auto; intros.
        { specialize (IHgs _ Htacs _ H0).
          rewrite H1 in IHgs.
          forward_reason.
          split; auto.
          forward.
          rewrite list_mapT_cons in H6.
          forward. inv_all; subst.
          erewrite substD_conv with (pfv := eq_sym (app_nil_r_trans tvs))
                                    (pfu := eq_sym (app_nil_r_trans tus)) in H8.
          autorewrite with eq_rw in H8.
          forward. inv_all; subst.
          eapply H11 in H12; clear H11; eauto.
          eapply H9 in H13; clear H9; eauto.
          intuition.
          exists Hnil.
          intro vs'; rewrite (hlist_eta vs'); clear vs'.
          do 2 rewrite hlist_app_nil_r.
          destruct (eq_sym (app_nil_r_trans tus)).
          destruct (eq_sym (app_nil_r_trans tvs)).
          intuition. }
        { specialize (IHgs _ Htacs _ H0).
          rewrite H1 in IHgs.
          forward_reason; split; auto.
          unfold stateD in *.
          forward.
          rewrite list_mapT_cons in *.
          forward. inv_all; subst.
          erewrite substD_conv with (pfv := eq_sym (app_nil_r_trans tvs))
                                    (pfu := eq_sym (app_nil_r_trans tus)) in H8.
          autorewrite with eq_rw in H8.
          forward. inv_all; subst.
          eapply H13 in H14; eauto; clear H13.
          eapply H9 in H15; eauto; clear H9.
          intuition.
          exists Hnil.
          intro vs'; rewrite (hlist_eta vs'); clear vs'.
          do 2 rewrite hlist_app_nil_r.
          destruct (eq_sym (app_nil_r_trans tus)).
          destruct (eq_sym (app_nil_r_trans tvs)).
          intuition. } }
      { destruct gs; auto.
        clear IHgs.
        eapply stac_sound_More in H0; eauto.
        forward_reason; split; auto.
        unfold stateD in *.
        forward.
        rewrite list_mapT_cons in H3.
        rewrite list_mapT_nil in H3.
        forward.
        inv_all; subst.
        eapply H6 in H10; auto.
        forward_reason; auto. } }
  Qed.

End parameterized.
