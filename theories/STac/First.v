Require Import Coq.Lists.List.
Require Import MirrorCore.STac.Core.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Definition FIRST (brs : list (stac typ expr subst)) : stac typ expr subst :=
    fun tus tvs sub e =>
      (fix FIRST (brs : list (stac typ expr subst)) : Result typ expr subst :=
         match brs with
           | nil => @Fail _ _ _
           | br :: brs =>
             match br tus tvs sub e with
               | Fail => FIRST brs
               | x => x
             end
         end) brs.

  Theorem FIRST_sound
  : forall brs, Forall (@stac_sound _ _ _) brs ->
                stac_sound (FIRST brs).
  Proof.
    induction 1.
    { red. simpl. auto. }
    { red. simpl. intros.
      specialize (H tus tvs s g).
      destruct (x tus tvs s g); eauto.
      eapply IHForall. }
  Qed.

End parameterized.
