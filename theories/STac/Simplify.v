Require Import MirrorCore.STac.Core.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Definition SIMPLIFY
             (f : list typ -> list typ -> expr -> expr)
             (thn : stac typ expr subst)
  : stac typ expr subst :=
    fun e s tus tvs =>
      thn (f tus tvs e) s tus tvs.

End parameterized.
