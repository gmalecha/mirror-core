Require Import MirrorCore.STac.Core.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Definition TRY (b : stac typ expr subst) : stac typ expr subst :=
    fun tus tvs sub e =>
      match b tus tvs sub e with
        | Fail => More tus tvs sub e
        | x => x
      end.

  Theorem TRY_sound : forall b, stac_sound b -> stac_sound (TRY b).
  Proof.
    unfold stac_sound; intros.
    specialize (H tus tvs s g). unfold TRY.
    destruct (b tus tvs s g); auto.
  Qed.

End parameterized.
