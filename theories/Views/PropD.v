Require Import MirrorCore.Views.TrmD.

Section PropD.
  Context {typ : Type} {RType_typ : RType typ}.
  
  Context {Typ0_tyProp : Typ0 _ Prop}.

  Let tyProp : typ := @typ0 _ _ _ Typ0_tyProp.

  Definition PropR (P : Prop) : typD tyProp :=
    trmR P (typ0_cast (Typ0 := Typ0_tyProp)).

  Definition PropD (P : typD tyProp) : Prop :=
    trmD P (typ0_cast (Typ0 := Typ0_tyProp)).

End PropD.