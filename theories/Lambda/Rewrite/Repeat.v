Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relations.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.Util.Compat.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.RewriteRelations.
Require Import MirrorCore.Lambda.Rewrite.Core.

Set Implicit Arguments.
Set Strict Implicit.

Set Suggest Proof Using.

Section setoid.
  Context {typ : Type}.
  Context {func : Type}.
  Context {RType_typD : RType typ}.
  Context {Typ2_Fun : Typ2 RType_typD RFun}.
  Context {RSym_func : RSym func}.

  (** Reasoning principles **)
  Context {RTypeOk_typD : RTypeOk}.
  Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.
  Context {RSymOk_func : RSymOk RSym_func}.
  Context {Typ0_Prop : Typ0 _ Prop}.

  Local Existing Instance Subst_ctx_subst.
  Local Existing Instance SubstOk_ctx_subst.
  Local Existing Instance SubstUpdate_ctx_subst.
  Local Existing Instance SubstUpdateOk_ctx_subst.
  Local Existing Instance Expr_expr.
  Local Existing Instance ExprOk_expr.

  (* TODO(gmalecha): Wrap all of this up in a type class?
   * Why should it be different than Expr?
   *)
  Variable Rbase : Type.
  Variable Rbase_eq : Rbase -> Rbase -> bool.
  Hypothesis Rbase_eq_ok : forall a b, Rbase_eq a b = true -> a = b.

  Local Notation "'R'" := (R typ Rbase).

  Variable RbaseD : Rbase -> forall t : typ, option (typD t -> typD t -> Prop).

  (** Apply the same rewrite until it stops making progress
   **)

  Variable rw : RwAction typ func Rbase.
  Variable is_refl : refl_dec R.
  Variable is_trans : trans_dec R.

  Local Fixpoint repeat_rewrite' (n : nat)
           (prog : expr typ func -> Progressing (expr typ func))
           (e : expr typ func) (r : R)
  : mrw typ func (Progressing (expr typ func)) :=
    match n with
    | 0 => if is_refl r
           then rw_ret (prog e)
           else rw_fail
    | S n => rw_bind_catch
               (rw e r)
               (fun e' =>
                  match e' with
                  | NoProgress =>
                    if is_refl r then rw_ret (prog e) else rw_fail
                  | Progress e' as X =>
                    if is_trans r then repeat_rewrite' n (@Progress _) e' r
                    else rw_ret X
                  end)
               (if is_refl r
                then rw_ret (prog e)
                else rw_fail)
    end.

  Hypothesis rw_sound : setoid_rewrite_spec RbaseD rw.
  Hypothesis is_reflOk : refl_dec_ok (RD RbaseD) is_refl.
  Hypothesis is_transOk : trans_dec_ok (RD RbaseD) is_trans.

  Local Lemma repeat_rewrite'_mono : forall n e r c A B C D E F X Y,
      repeat_rewrite' (c:=c) n (@Progress _) e r A B C D E F = Some (X,Y) ->
      X <> NoProgress.
  Proof using.
    induction n; simpl.
    { intros. destruct (is_refl r). inversion H. congruence. inversion H. }
    { intros.
      eapply rw_bind_catch_case in H. destruct H; forward_reason.
      { destruct x.
        { destruct (is_trans r); eauto.
          inversion H0. congruence. }
        { destruct (is_refl r).
          { inversion H0; congruence. }
          { inversion H0. } } }
      { destruct (is_refl r).
        { inversion H; congruence. }
        { inversion H. } } }
  Qed.

  Local Theorem repeat_rewrite'_sound
  : forall n (prog : bool),
      setoid_rewrite_spec
        RbaseD
        (repeat_rewrite' n
                         (if prog then @Progress _ else (fun _ => NoProgress))).
  Proof using is_reflOk is_transOk rw_sound.
    induction n.
    { intros. simpl. destruct prog.
      { do 2 red. intros.
        specialize (@is_reflOk r).
        destruct (is_refl r).
        { inversion H; clear H; subst.
          split; auto.
          intros.
          eapply is_reflOk in H; trivial.
          simpl.
          forward.
          split; [ reflexivity | ].
          intros. eapply Pure_pctxD; eauto. }
        { inversion H. } }
      { do 2 red; intros.
        specialize (@is_reflOk r).
        destruct (is_refl r).
        { inversion H; clear H; subst.
          split; auto.
          intros.
          eapply is_reflOk in H; eauto.
          simpl. forward.
          split; [ reflexivity | ].
          intros; eapply Pure_pctxD; eauto. }
        { inversion H. } } }
    { simpl. do 2 red; intros.
      eapply rw_bind_catch_case in H; destruct H; forward_reason.
      { eapply rw_sound in H.
        forward_reason. destruct x.
        { specialize (@is_transOk r).
          destruct (is_trans r).
          { generalize (repeat_rewrite'_mono _ _ _ _ _ _ _ _ _ H1).
            eapply (IHn true) in H1.
            forward_reason. split; auto.
            intros.
            specialize (H3 _ _ H5).
            specialize (H2 _ _ H5).
            simpl in *.
            forward.
            forward_reason.
            destruct e'; simpl in *.
            { Cases.rewrite_all_goal.
              split; [ reflexivity | ].
              intros. gather_facts.
              eapply pctxD_SubstMorphism; [ | | eassumption | ]; eauto.
              gather_facts.
              eapply is_transOk in H5; eauto.
              eapply Pure_pctxD; eauto. }
            { congruence. } }
          { inversion H1; clear H1; subst.
            simpl in *. split; auto. } }
        { specialize (@is_reflOk r).
          destruct (is_refl r); [ | inversion H1 ].
          inversion H1; clear H1; subst.
          split; auto.
          intros. specialize (H2 _ _ H1).
          forward. destruct prog; simpl in *.
          { rewrite H5. forward_reason.
            split; auto. }
          { rewrite H5; forward_reason; auto. } } }
      { specialize (@is_reflOk r).
        destruct (is_refl r); [ | inversion H ].
        inversion H; clear H; subst.
        split; auto.
        intros.
        forward.
        cutrewrite (ProgressD e
                              ((if prog then (@Progress _)
                                else fun _ : expr typ func => NoProgress) e) = e);
          [ | destruct prog; reflexivity ].
        rewrite H3; forward_reason.
        split; [ reflexivity | ].
        eapply is_reflOk in H; eauto.
        eapply Pure_pctxD; eauto. } }
  Qed.

  Definition repeat_rewrite (progress : bool)
  : nat -> RwAction typ func Rbase :=
    let prog := if progress then @Progress _ else (fun _ => NoProgress) in
    fun n =>
      repeat_rewrite' n prog.

  Theorem repeat_rewrite_sound
  : forall b n, setoid_rewrite_spec RbaseD (repeat_rewrite b n).
  Proof using is_reflOk is_transOk rw_sound.
    unfold repeat_rewrite. simpl. intros.
    eapply repeat_rewrite'_sound.
  Qed.

End setoid.
