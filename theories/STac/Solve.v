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
        | Solve s => @Solve _ _ _ s
        | x => @Fail _ _ _
      end.

End parameterized.
