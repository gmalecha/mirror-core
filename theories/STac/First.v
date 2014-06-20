Require Import Coq.Lists.List.
Require Import MirrorCore.STac.Core.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Definition FIRST (brs : list (stac typ expr subst)) : stac typ expr subst :=
    fun e sub tus tvs =>
      (fix FIRST (brs : list (stac typ expr subst)) : Result typ expr subst :=
         match brs with
           | nil => @Fail _ _ _
           | br :: brs =>
             match br e sub tus tvs with
               | Fail => FIRST brs
               | x => x
             end
         end) brs.

End parameterized.
