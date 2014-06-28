Require Import MirrorCore.STac.Core.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Definition IDTAC : stac typ expr subst := @More _ _ _.

  Theorem IDTAC_sound : stac_sound IDTAC.
  Proof.
    red; intros; simpl; auto.
  Qed.

End parameterized.
