Require Import ExtLib.Structures.Logic.

Set Implicit Arguments.
Set Strict Implicit.

Section sl.
  Variable L P : Type.

  Class SeparationLogic : Type :=
  { emp : P
  ; star : P -> P -> P
  ; himp : P -> P -> L
  }.

  Variable sl : SeparationLogic.
  Variable Logic_L : Logic L.
  Variable LL_L : LogicLaws Logic_L.
  Variable Quant_L : Quant L.

  Class SeparationLogic_Laws : Type :=
  { star_emp_p : Entails nil (All (fun p => himp (star p emp) p))
  ; star_emp_c : Entails nil (All (fun p => himp p (star p emp)))
  ; star_comm : Entails nil (All (fun p => All (fun q => himp (star p q) (star q p))))
  ; star_assoc : Entails nil (All (fun p => All (fun q => All (fun r =>
       himp (star (star p q) r) (star p (star q r))))))
  }.

End sl.

Section syntax.
  Require Import MirrorCore.Repr.
  Require Import MirrorCore.Expr.

  Variable L S : Type.
  Variable SL : SeparationLogic L S.
  Variable QSL : Quant S.

  Definition sl_types : Repr type :=
    listToRepr (default_type L :: default_type S :: nil) (empty_type).

  Definition sl_repr ts : Repr (function (repr sl_types ts)) :=
    let ts := repr sl_types ts in
    let s := tvType 1 in
    let l := tvType 0 in
    listToRepr (F ts 0 s (@emp _ _ SL) ::
                F ts 0 (tvArr s (tvArr s s)) (@star _ _ SL) ::
                F ts 1 (tvArr (tvArr (tvVar 0) s) s) (@Ex _ _) ::
                nil) (F ts 0 tvProp False).

  Section cases.
    Variable ts : types.
    Variable R : Type.
    Hypothesis caseEmp : unit -> R.
    Hypothesis caseStar : expr (repr sl_types ts) -> expr (repr sl_types ts) -> R.
    Hypothesis caseEx : typ -> expr -> (repr sl_types ts) -> R.

  Definition matchSepLog ts (e : expr (repr sl_types)) : 