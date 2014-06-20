Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.SubstI3.
Require Import MirrorCore.EProver2.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  (** TODO: I'm going to need to thread facts for a prover through here **)
  Variable subst : Type.

  Inductive Result : Type :=
  | Fail
  | Solve : subst -> Result
  | Progress : expr -> subst -> list typ -> list typ -> Result.

  Definition stac : Type :=
    expr -> subst -> list typ -> list typ ->
    Result.

End parameterized.
