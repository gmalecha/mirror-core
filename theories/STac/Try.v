Require Import ExtLib.Data.HList.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.SubstI3.
Require Import MirrorCore.EProver2.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.LemmaApply.
Require Import MirrorCore.Util.Iteration.
Require Import MirrorCore.Subst.FastSubst.
Require Import MirrorCore.STac.Core.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Definition TRY (b : branch typ expr subst) : branch typ expr subst :=
    fun e sub tus tvs =>
      match b e sub tus tvs with
        | Fail => Progress e sub tus tvs
        | x => x
      end.

End parameterized.
