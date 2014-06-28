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
  Variable subst : Type.

  Definition REPEAT (max : nat) (br : stac typ expr subst)
  : stac typ expr  subst :=
    (fix DO (n : nat) : stac typ expr  subst :=
       match n with
         | 0 => @More _ _ _
         | S n =>
           fun tus tvs sub e =>
             match br tus tvs sub e with
               | Fail => More tus tvs sub e (** Never fails **)
               | More e sub tus tvs => DO n e sub tus tvs
               | Solved s => @Solved _ _ _ s
             end
       end) max.

  Theorem REPEAT_sound
  : forall br, stac_sound br ->
               forall n,
                 stac_sound (REPEAT n br).
  Proof.
    induction n; simpl.
    { red. auto. }
    { red. intros.
      specialize (H tus tvs s g).
      destruct (br tus tvs s g); auto.
      red in IHn. specialize (IHn l l0 s0 e).
      destruct (REPEAT n br l l0 s0 e); auto. }
  Qed.

End parameterized.
