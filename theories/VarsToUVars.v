Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.Nat.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.VariablesI.
Require Import MirrorCore.CtxLogic.

Set Implicit Arguments.
Set Strict Implicit.

Section vars_to_uvars.
  Variable typ : Type.
  Variable expr : Type.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Expr_expr : @Expr typ _ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.
  Context {ExprUVar_expr : ExprUVar expr}.
  Context {ExprUVarOk_expr : ExprUVarOk _}.


  Definition vars_to_uvars (skip add : nat) (e : expr) : expr :=
    @expr_subst _ _ _ _
                (fun _ => None)
                (fun v => Some (UVar (add + v))) skip e.

  Definition vars_to_uvars_spec
             (vars_to_uvars : nat -> nat -> expr -> expr)
  : Prop :=
    forall (tus : tenv typ) (e : expr) (tvs : list typ)
           (t : typ) (tvs' : list typ)
           (val : hlist typD tus ->
                  hlist typD (tvs ++ tvs') -> typD t),
      exprD' tus (tvs ++ tvs') e t = Some val ->
      exists
        val' : hlist typD (tus ++ tvs') ->
               hlist typD tvs -> typD t,
        exprD' (tus ++ tvs') tvs (vars_to_uvars (length tvs) (length tus) e)
               t = Some val' /\
        (forall (us : hlist typD tus)
                (vs' : hlist typD tvs') (vs : hlist typD tvs),
           val us (hlist_app vs vs') = val' (hlist_app us vs') vs).

  Theorem vars_to_uvars_sound
  : vars_to_uvars_spec vars_to_uvars.
  Proof.
    red. intros.
    remember (vars_to_uvars (length tvs) (length tus) e) as e'.
    symmetry in Heqe'.
    eapply expr_subst_sound
      with (tus:=tus) (tvs:=tvs') (tus':=tus++tvs') (tvs':=nil) (_tvs:=tvs)
           (R:=fun us vs us' vs' =>
                 us' = hlist_app us vs)
        in Heqe'; eauto.
    { forward_reason.
      rewrite exprD'_conv with (pfu:=eq_refl) (pfv:=eq_sym (app_nil_r_trans _)) in H0.
      autorewrite with eq_rw in H0.
      forward.
      eexists; split; eauto. inv_all; subst.
      intros. specialize (H1 us vs' (hlist_app us vs') Hnil vs eq_refl).
      rewrite hlist_app_nil_r in H1.
      autorewrite with eq_rw in H1.
      assumption. }
    { intros.
      eapply nth_error_get_hlist_nth_weaken with (ls':=tvs') in H0.
      simpl in *.
      forward_reason. eexists; split; eauto.
      intros. subst; eauto. }
    { intros.
      generalize (@UVar_exprD' typ expr _ _ _ _ (tus ++ tvs') nil (length tus + u) t0).
      match goal with
        | |- context [ match ?X with _ => _ end ] => destruct X
      end.
      { intros; forward_reason.
        eapply nth_error_get_hlist_nth_appR in H1; [ | omega ].
        simpl in H1.
        eexists; split; eauto. intros; subst.
        replace (length tus + u - length tus) with u in H1 by omega.
        rewrite H0 in H1.
        forward_reason. inv_all. subst.
        erewrite <- H3.
        eapply H2. }
      { intro. exfalso.
        eapply nth_error_get_hlist_nth_Some in H0. destruct H0; clear H0.
        rewrite ListNth.nth_error_app_R in H1; [ | omega ].
        replace (length tus + u - length tus) with u in H1 by omega.
        destruct H1.
        { simpl in x. congruence. }
        { simpl in *. forward_reason.
          rewrite x in H0. inv_all. apply H1. subst.
          eapply Rrefl. } } }
  Qed.

End vars_to_uvars.

Arguments vars_to_uvars {typ expr RType Expr ExprUVar} _ _ _ : rename.