Require Import MirrorCore.TypesI.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Section PropD.
  Context {typ : Type} {RType_typ : RType typ}.
  
  Context {Typ0_tyProp : Typ0 _ Prop}.

  Let tyProp : typ := @typ0 _ _ _ Typ0_tyProp.

  Definition PropR (P : Prop) : typD tyProp :=
    castR id Prop P.

  Definition PropD (P : typD tyProp) : Prop :=
    castD id Prop P.

End PropD.