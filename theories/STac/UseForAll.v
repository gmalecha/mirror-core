Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
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

  Section apply_to_all.
    Variable tac : stac typ expr subst.
    Variables tus tvs : list typ.

    Fixpoint apply_to_all'
             (sub : subst) (hs : list expr) (es : list expr)
             {struct es}
    : Result typ expr subst :=
      match es with
        | nil => @Solved _ _ _ nil nil sub
        | e :: es =>
          match tac tus tvs sub hs e with
            | Solved nil nil sub' =>
              apply_to_all' sub' hs es
            | More tus tvs sub hs e =>
              match es with
                | nil => More tus tvs sub hs e
                | _ => (** TODO: This could be more liberal **)
                  @Fail _ _ _
              end
            | _ => @Fail _ _ _
          end
      end.

  End apply_to_all.

  Definition apply_to_all : stac typ expr subst -> stac_cont typ expr subst :=
    apply_to_all'.

  Lemma mapT_nil
  : forall (T U : Type) (F : T -> option U),
      mapT F nil = Some nil.
  Proof. reflexivity. Defined.

  Lemma mapT_cons
  : forall T U (F : T -> option U) l ls,
      mapT F (l :: ls) = match F l , mapT F ls with
                           | Some l , Some ls => Some (l :: ls)
                           | _ , _ => None
                         end.
  Proof.
    simpl. intros. destruct (F l); reflexivity.
  Qed.

  Theorem apply_to_all_sound
  : forall tac, stac_sound tac ->
                stac_cont_sound (apply_to_all tac).
  Proof.
    Opaque mapT.
    red.
    intros tac Htac tus tvs sub hyps gs; revert sub.
    induction gs; simpl; intros; auto.
    { split; auto.
      forward.
      erewrite substD_conv with (pfv := eq_sym (app_nil_r_trans tvs))
                                (pfu := eq_sym (app_nil_r_trans tus)).
      rewrite H2.
      unfold ResType.
      repeat rewrite eq_option_eq.
      intros. forward_reason.
      rewrite (hlist_eta x) in *; clear x.
      rewrite (hlist_eta x0) in *; clear x0.
      do 2 rewrite hlist_app_nil_r in H3.
      destruct (eq_sym (app_nil_r_trans tvs)).
      destruct (eq_sym (app_nil_r_trans tus)).
      intuition.
      rewrite mapT_nil in H1.
      inv_all; subst. constructor. }
    { consider (tac tus tvs sub hyps a); auto; intros.
      { eapply stac_sound_Solved in H0; eauto.
        forward_reason.
        forward. subst.
        consider (apply_to_all tac tus tvs s hyps gs); auto; intros.
        { specialize (IHgs _ H0).
          rewrite H1 in IHgs.
          forward_reason.
          split; auto.
          forward.
          rewrite mapT_cons in H6.
          forward. inv_all; subst.
          erewrite substD_conv with (pfv := eq_sym (app_nil_r_trans tvs))
                                    (pfu := eq_sym (app_nil_r_trans tus)) in H8.
          unfold ResType in H8.
          repeat rewrite eq_option_eq in H8.
          forward. inv_all; subst.
          eapply H11 in H12; clear H11; eauto.
          eapply H9 in H13; clear H9; eauto.
          intuition.
          exists Hnil; exists Hnil.
          do 2 rewrite hlist_app_nil_r.
          destruct (eq_sym (app_nil_r_trans tus)).
          destruct (eq_sym (app_nil_r_trans tvs)).
          intuition. }
        { specialize (IHgs _ H0).
          rewrite H1 in IHgs.
          forward_reason; split; auto.
          forward.
          rewrite mapT_cons in *.
          forward. inv_all; subst.
          erewrite substD_conv with (pfv := eq_sym (app_nil_r_trans tvs))
                                    (pfu := eq_sym (app_nil_r_trans tus)) in H8.
          unfold ResType in H8.
          repeat rewrite eq_option_eq in H8.
          forward. inv_all; subst.
          eapply H13 in H14; eauto; clear H13.
          eapply H9 in H15; eauto; clear H9.
          intuition.
          exists Hnil; exists Hnil.
          do 2 rewrite hlist_app_nil_r.
          destruct (eq_sym (app_nil_r_trans tus)).
          destruct (eq_sym (app_nil_r_trans tvs)).
          intuition. } }
      { destruct gs; auto.
        clear IHgs.
        eapply stac_sound_More in H0; eauto.
        forward_reason; split; auto.
        forward.
        rewrite list_mapT_cons in H3.
        rewrite list_mapT_nil in H3.
        forward.
        inv_all; subst.
        eapply H8 in H9; auto.
        forward_reason; auto. } }
  Qed.

End parameterized.
