Require Import MirrorCore.STac.Core.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Definition SIMPLIFY
             (f : list typ -> list typ -> subst -> expr -> expr)
  : stac typ expr subst :=
    fun tus tvs s e =>
      More tus tvs s (f tus tvs s e).

  Theorem SIMPLIFY_sound
  : forall f,
      (forall tus tvs s e e',
         f tus tvs s e = e' ->
         goalD tus tvs s e' -> goalD tus tvs s e) ->
      stac_sound (SIMPLIFY f).
  Proof.
    intros. unfold stac_sound, SIMPLIFY.
    intros. eapply H. reflexivity. eauto.
  Qed.

End parameterized.
