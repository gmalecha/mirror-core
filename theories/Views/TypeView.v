Require Import ExtLib.Tactics.
Require Import ExtLib.Data.POption.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Views.View.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.syms.SymProd.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.
Set Universe Polymorphism.

Section TypeView.
  Universes s v.
  Variables typ1 typ2 : Type@{s}.
  Variable FV : PartialView typ1 typ2.
  Variable typ1D : typ1 -> Type@{v}.
  Variable typ2D : typ2 -> Type@{v}.

  Definition type_equiv (f : typ1) (a : typ2) : Prop :=
    typ1D f = typ2D a.

  Variable PV : PartialView typ1 typ2.

  Definition TypeViewOk : Type :=
    PartialViewOk PV type_equiv.
End TypeView.

Export MirrorCore.Views.View.