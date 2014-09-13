Require Import Coq.PArith.BinPos.
Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.Try.
Require Import MirrorCore.RTac.Idtac.
Require Import MirrorCore.RTac.Then.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Subst_subst : Subst subst expr}.
  Context {SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst}.
  Context {SubstUpdate_subst : SubstUpdate subst expr}.

  Section repeater.
    (** TODO: To be efficient, this must be written in CPS
     **)
    Fixpoint REPEAT' (n : positive) (tac : rtac typ expr subst)
             {struct n}
    : rtac typ expr subst :=
      fun ctx sub gl =>
        match n with
          | xH => TRY tac ctx sub gl
          | xI n => match tac ctx sub gl with
                      | Fail => IDTAC ctx sub gl
                      | More sub gl' =>
                        let '(tus,tvs) := Open.getEnvs ctx in
                        RunOnGoal (REPEAT' n tac) ctx gl' (length tus) (length tvs)
(*
                          | None => Some gl'
                          | Some gl'' => TRY (REPEAT' n tac) gl''
                        end *)
                      | x => x
                    end
          | xO n => match REPEAT' n tac ctx sub gl with
                      | Fail => IDTAC ctx sub gl
                      | More sub gl' =>
                        let '(tus,tvs) := Open.getEnvs ctx in
                        RunOnGoal (REPEAT' n tac) ctx gl' (length tus) (length tvs)
                      | x => x
                    end
        end.
  End repeater.

  Definition REPEAT n (tac : rtac typ expr subst)
  : rtac typ expr subst :=
    REPEAT' n tac.

  Theorem REAPEAT_sound
  : forall tus tvs n tac, rtac_sound tus tvs tac ->
                          rtac_sound tus tvs (REPEAT n tac).
  Proof.
  Admitted.

End parameterized.
