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
  (** TODO: I might want some way to maintain external state **)
  Variable subst : Type.

  Inductive Result : Type :=
  | Fail
  | Solved : subst -> Result
  | More : list typ -> list typ -> subst -> expr -> Result.

  Definition stac : Type :=
    (** TODO: Part of the state is hypotheses **)
    list typ -> list typ -> subst -> expr ->
    Result.

  Axiom goalD : forall (tus tvs : list typ) (s : subst) (goal : expr), Prop.

  Definition stac_sound (tac : stac) : Prop
  := forall tus tvs s (g : expr),
       match tac tus tvs s g with
         | Fail => True
         | Solved s' =>
           goalD tus tvs s g (* /\ Extends s' s *)
         | More tus' tvs' s' g' =>
           goalD tus' tvs' s' g' ->
           goalD tus tvs s g
       end.

End parameterized.
