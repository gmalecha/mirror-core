Require Import MirrorCore.STac.Core.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Definition TRY (b : branch typ expr subst) : branch typ expr subst :=
    fun e sub tus tvs =>
      match b e sub tus tvs with
        | Fail => Progress e sub tus tvs
        | x => x
      end.

End parameterized.
