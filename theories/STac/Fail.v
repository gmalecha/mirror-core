Require Import MirrorCore.STac.Core.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Definition FAIL : stac typ expr subst :=
    fun _ _ _ _ =>
      @Fail _ _ _.

End parameterized.
