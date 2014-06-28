Require Import MirrorCore.STac.Core.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Definition THEN (a b : stac typ expr subst) : stac typ expr subst :=
    fun e sub tus tvs =>
      let res := a e sub tus tvs in
      match res with
        | Solved s => @Solved _ _ _ s
        | More e sub tus tvs => b e sub tus tvs
        | Fail => res
      end.

  Theorem THEN_sound
  : forall a b, stac_sound a -> stac_sound b -> stac_sound (THEN a b).
  Proof.
    unfold stac_sound, THEN; intros.
    specialize (H tus tvs s g).
    destruct (a tus tvs s g); auto.
    specialize (H0 l l0 s0 e).
    destruct (b l l0 s0 e); auto.
  Qed.

End parameterized.
