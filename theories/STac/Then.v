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
        | Solve s => @Solve _ _ _ s
        | Progress e sub tus tvs => b e sub tus tvs
        | Fail => res
      end.

End parameterized.
