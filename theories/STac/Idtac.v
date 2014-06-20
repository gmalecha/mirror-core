Require Import MirrorCore.STac.Core.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Definition IDTAC : stac typ expr subst :=
    fun e sub tus tvs =>
      Progress e sub tus tvs.

End parameterized.
