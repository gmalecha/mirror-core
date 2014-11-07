Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.RunOnGoals.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.

  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.

  (** TODO: Write this with a positive **)
  Section repeater.
    (** TODO: To be efficient, this must be written in CPS
     **)
    Variable tac : rtac typ expr.

    Fixpoint REPEAT' (n : nat) {struct n}
    : rtac typ expr :=
      fun tus tvs nus nvs ctx sub gl =>
        match n with
          | 0 => More_ sub (GGoal gl)
          | S n =>
            match @tac tus tvs nus nvs ctx sub gl with
              | Fail => More_ sub (GGoal gl)
              | More_ sub' gl' =>
                runOnGoals (fun x => REPEAT' n x) tus tvs nus nvs _ sub' gl'
              | Solved s => Solved s
            end
        end.
  End repeater.

  Definition REPEAT n (tac : rtac typ expr)
  : rtac typ expr :=
    REPEAT' tac n.

  Theorem REPEAT_sound
  : forall n tac, rtac_sound tac ->
                  rtac_sound (REPEAT n tac).
  Proof.
    unfold REPEAT. intros n tac H.
    induction n.
    - simpl. clear.
      red; intros; subst.
      eapply rtac_spec_More_.
    - simpl. red; intros; subst.
      specialize (H ctx s g _ eq_refl).
      destruct (tac (getUVars ctx) (getVars ctx)
                    (length (getUVars ctx)) (length (getVars ctx))
                    ctx s g); auto using rtac_spec_More_.
      eapply rtac_spec_trans; eauto.
      eapply runOnGoals_sound; eauto with typeclass_instances.
  Qed.

End parameterized.


(*
  Section repeater.
    (** TODO: To be efficient, this must be written in CPS
     **)
    Variable tac : rtac typ expr subst.

    Fixpoint REPEAT' (n : positive)
             (onDone : Result typ expr subst -> Result typ expr subst)
             (onContinue : Ctx typ expr -> subst -> Goal typ expr -> Result typ expr subst)
             {struct n}
    : Ctx typ expr -> subst -> expr -> Result typ expr subst :=
      fun ctx sub gl =>
        match n with
          | xH => tac ctx sub gl
          | xI n =>
            match tac ctx sub gl with
              | Fail => onDone (More sub (GGoal gl))
              | More sub' gl' =>
                runRTac (REPEAT' n onDone
                                 (fun ctx' sub' gl' =>
                                    runRTac (REPEAT' n onDone onContinue)
                                            ctx' sub' gl'))
                        ctx sub' gl'
              | Solved s => onDone (Solved s)
            end
          | xO n =>
            REPEAT' n onDone
                    (fun ctx' sub' gl' =>
                       runRTac (REPEAT' n onDone onContinue)
                               ctx' sub' gl')
           ctx sub gl
        end.
  End repeater.
*)