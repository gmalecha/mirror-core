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

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Variable RType_typ : RType typ.
  Variable Expr_expr : Expr RType_typ expr.
  Variable Typ0_Prop : Typ0 _ Prop.
  Variable Subst_subst : Subst subst expr.
  Variable SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst.

  Section repeater.
    Require Import Coq.PArith.BinPos.

    Fixpoint REPEAT' (n : positive) (tac : rtac typ expr subst)
             {struct n}
    : rtac typ expr subst :=
      fun gl =>
        match n with
          | xH => tac gl
          | xI n => match tac gl with
                      | None => Some gl
                      | Some gl' =>
                        match REPEAT' n tac gl' with
                          | None => Some gl'
                          | Some gl'' => REPEAT' n tac gl'
                        end
                    end
          | xO n => match REPEAT' n tac gl with
                      | None => Some gl
                      | Some gl' => REPEAT' n tac gl
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
