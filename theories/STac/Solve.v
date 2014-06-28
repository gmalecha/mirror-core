Require Import MirrorCore.STac.Core.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Definition SOLVE (b : stac typ expr subst) : stac typ expr subst :=
    fun e sub tus tvs =>
      match b e sub tus tvs with
        | Solved s => @Solved _ _ _ s
        | x => @Fail _ _ _
      end.

  Theorem SOLVE_sound : forall t, stac_sound t -> stac_sound (SOLVE t).
  Proof.
    unfold stac_sound; simpl; intros.
    red. specialize (H tus tvs s g).
    destruct (t tus tvs s g); auto.
  Qed.

End parameterized.
