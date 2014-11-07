Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.LemmaApply.
Require Import MirrorCore.InstantiateI.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.Reduce.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.

  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.

  Variable UVar : nat -> expr.
  Variable vars_to_uvars : nat -> nat -> expr -> expr.
  Variable exprUnify : forall subst, Subst subst expr -> SubstUpdate subst expr ->
    tenv typ -> tenv typ -> nat -> expr -> expr -> typ -> subst -> option subst.
  Variable instantiate : (nat -> option expr) -> nat -> expr -> expr.
  Variable UVar : nat -> expr.

  Variable lem : Lemma.lemma typ expr expr.

  Definition freshUVars (ts : list typ) (c : Ctx typ expr) (s : ctx_subst c)
  : ctx_subst (CExs c ts) :=
    ExsSubst s (amap_empty _).

  Definition EAPPLY : rtac typ expr :=
    let len_vars := length lem.(vars) in
    fun tus tvs nus nvs ctx sub goal =>
      match @eapplicable typ _ expr _
                         _ (* (ctx_subst (CExs ctx lem.(vars))) *)
                         vars_to_uvars
                         (@exprUnify _ _ (SubstUpdate_ctx_subst instantiate _))
                         (freshUVars lem.(vars) sub)
                         tus tvs lem goal
      with
        | None => Fail
        | Some sub' =>
          let len_uvars := length tus in
          let premises := map (fun x => GGoal (vars_to_uvars 0 len_uvars x)) lem.(premises) in
          reduceGoal instantiate UVar (fold_left (@CEx _ _) lem.(vars) CTop) sub'
                     (GConj premises) (countUVars ctx + len_vars) (countVars ctx)
      end.

  Hypothesis lemD :
    @Lemma.lemmaD typ expr _ _ expr (@exprD'_typ0 _ _ _ _ Prop _)
                  _ nil nil lem.

  Theorem EAPPLY_sound : rtac_sound EAPPLY.
  Proof.
    red. unfold EAPPLY. intros.
    subst. unfold rtac_spec. forward.
    (** Soundness of [reduceGoal]!
     ** 
     **)

    Theorem reduceGoal_sound
    : forall ctx ctx' sub sub' gl,
        @rtac_spec typ expr _ _ _ ctx sub' gl
                   (@reduceGoal typ expr ctx ctx' sub gl 0 0).
    Proof.
      About rtac_spec.
      unfold rtac_spec. unfold reduceGoal.
      induction ctx'; simpl; intros.
      { (* Top *)
        Print rtac_spec.

End parameterized.
