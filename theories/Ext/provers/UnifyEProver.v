Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprProp.
Require Import MirrorCore.Iso.
Require Import MirrorCore.SymI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.EProver.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.ExprUnifySyntactic.

Set Implicit Arguments.
Set Strict Implicit.

Section parameters.
  Variable types : Types.types.
  Variable func : Type.
  Variable RSym_func : RSym (typD types) func.
  Variable RSymOk_func : RSymOk RSym_func.

  Variable is_equal : expr func -> option (typ * expr func * expr func).
  Hypothesis is_equalOk : forall e t l r us vs val,
                            is_equal e = Some (t, l, r) ->
                            exprD us vs e tyProp = Some val ->
                            exists valL valR,
                              exprD us vs l t = Some valL /\
                              exprD us vs r t = Some valR /\
                              (val <-> valL = valR).
  Variable fuel : nat.

  Definition EProver_unify : @EProver typ (expr func) :=
  {| Facts := unit
   ; Summarize := fun _ _ _ => tt
   ; Learn := fun f _ _ _ => f
   ; Prove := fun _ Subst_sub _ tus tvs s e =>
                match is_equal e with
                  | Some (t,l,r) =>
                    @exprUnify _ types func RSym_func Subst_sub fuel tus tvs 0 s l r t
                  | None => None
                end
  |}.

  Theorem EProveOk_unify
  : forall (subst : Type) (Ssubst : Subst.Subst subst (expr func))
           (Sok : Subst.SubstOk (Expr_expr RSym_func) Ssubst),
      EProveOk (Provable_val (TypInstance0_tyProp types)) Sok
               (fun (_ _ : EnvI.env (typD types)) (_ : Facts EProver_unify) => True)
               (Prove EProver_unify (subst:=subst)).
  Proof.
    red; simpl; intros.

    forward.
    subst.
    eapply is_equalOk in H4; eauto.
    destruct H4 as [ ? [ ? [ ? [ ? ? ] ] ] ].
    subst.
    generalize (@exprUnify_sound subst _ _ RSym_func _ _ _ fuel
                                 (EnvI.typeof_env uvars) (EnvI.typeof_env vars)
                                 e0 e sub sub' t nil).
    simpl. intro.
    apply H7 in H5; eauto using typeof_expr_exprD.
    { clear H7. destruct H5.
      specialize (H7 uvars vars).
      destruct H7; auto.
      { apply WellTyped_env_typeof_env; reflexivity. }
      { apply WellTyped_env_typeof_env; reflexivity. }
      { specialize (H8 nil).
        simpl in *. split; auto.
        red. red. red. simpl. apply H4.
        rewrite H0 in *. rewrite H3 in *.
        match type of H8 with
          | ?X -> _ =>
            let H := fresh in assert (H : X) ; [ | specialize (H8 H) ]
        end.
        { apply WellTyped_env_typeof_env; reflexivity. }
        inv_all. assumption. } }
    { apply typeof_expr_exprD. eauto. }
    { apply typeof_expr_exprD. eauto. }
  Qed.

  Theorem EProverOk_unify
  : EProverOk (Provable_val (TypInstance0_tyProp types)) EProver_unify.
  Proof.
    refine (
        {| Valid := fun _ _ _ => True |}
      ).
    abstract auto.
    abstract auto.
    abstract auto.
    exact EProveOk_unify.
  Defined.
End parameters.