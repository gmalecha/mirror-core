Require Import ExtLib.Data.Sum.
Require Import ExtLib.Tactics.
Require Import MirrorCore.RTac.Core.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Context {typ : Type}.
  Context {expr : Type}.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.

  Variable simplify : forall subst : Type,
                        Subst subst expr ->
                        Ctx typ expr -> subst -> expr -> expr.

  Definition SIMPLIFY : rtac typ expr :=
    fun _ _ _ _ ctx sub gl =>
      More_ sub (GGoal (@simplify (ctx_subst ctx) _ ctx sub gl)).


  Hypothesis simplify_sound
  : forall (ctx : Ctx typ expr) (s : ctx_subst ctx) e e',
      @simplify (ctx_subst ctx) _ ctx s e = e' ->
      WellFormed_subst s ->
      match @pctxD typ expr RType_typ _ Expr_expr ctx s
          , ctx_substD (getUVars ctx) (getVars ctx) s (* necessary? *)
          , propD (getUVars ctx) (getVars ctx) e
          , propD (getUVars ctx) (getVars ctx) e'
      with
        | None , _ , _ , _ => True
        | _ , None , _ , _ => True
        | _ , _ , None , _ => True
        | _ , _ , _ , None => False
        | Some cD , Some sD , Some eD , Some eD' =>
          forall us vs,
            cD (fun us vs => sD us vs -> (eD' us vs -> eD us vs)) us vs
      end.

  Theorem SIMPLIFY_sound
  : forall tus tvs, rtac_sound tus tvs SIMPLIFY.
  Proof.
    red; intros; subst.
    simpl. intros; split; eauto.
    remember (simplify (Subst_ctx_subst ctx) ctx s g).
    symmetry in Heqe.
    specialize (@simplify_sound tus tvs _ _ _ _ Heqe).
    forward.
    destruct (Applicative_pctxD _ H0) as [ Hap Hpure ].
    eapply pctxD_substD in H0; eauto.
    forward_reason.
    rewrite H0 in *.
    forward.
    split.
    { reflexivity. }
    { intros. specialize (simplify_sound us vs); revert simplify_sound.
      eapply Hap. specialize (H2 us vs); revert H2.
      eapply Hap. eapply Hpure.
      clear. intros. tauto. }
  Qed.

End parameterized.
