Require Import MirrorCore.STac.Core.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Definition REC (n : nat) (b : stac typ expr subst -> stac typ expr subst)
             (last : stac typ expr subst)
  : stac typ expr subst :=
    (fix rec (n : nat) : stac typ expr subst :=
       match n with
         | 0 => b last
         | S n => fun e sub tus tvs =>
                    b (fun e sub tus tvs => rec n e sub tus tvs)
                      e sub tus tvs
       end) n.

End parameterized.
