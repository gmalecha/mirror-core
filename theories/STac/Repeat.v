Require Import ExtLib.Data.HList.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.SubstI3.
Require Import MirrorCore.Util.Iteration.
Require Import MirrorCore.STac.Core.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.

  Section repeat_branch.
    Variable subst : Type.

    Definition REPEAT (max : nat) (br : branch typ expr subst)
    : branch typ expr  subst :=
      (fix DO (n : nat) : branch typ expr  subst :=
         match n with
           | 0 => @Progress _ _ _
           | S n =>
             fun e sub tus tvs =>
               match br e sub tus tvs with
                 | Fail => Progress e sub tus tvs (** Never fails **)
                 | Progress e sub tus tvs => DO n e sub tus tvs
                 | Solve s => @Solve _ _ _ s
               end
         end) max.
  End repeat_branch.

End parameterized.
