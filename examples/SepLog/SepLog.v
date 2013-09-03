Require Import ExtLib.Structures.Logic.

Set Implicit Arguments.
Set Strict Implicit.

Section sl.
  Variable L P : Type.

  Class SeparationLogic : Type :=
  { emp : P
  ; star : P -> P -> P
  ; ex : forall t : Type, (t -> P) -> P
  ; inj : L -> P
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

Require Import ExtLib.Data.Vector.

Section syntax.
  Require Import List.
  Require Import MirrorCore.TypesI.
  Require Import MirrorCore.ExprI.

  Variable L S : Type.
  Variable SL : SeparationLogic L S.

  Variable typ : Type.
  Variable typD : list Type -> typ -> Type.
  Variable RType_typD : RType typD.

  Variable TI_Sep : TypInstance0 typD S.
  Variable TI_Prop : TypInstance0 typD L.

  Let tySep := @typ0 _ typD _ TI_Sep.
  Let tyProp := @typ0 _ typD _ TI_Prop.

  Variable expr : Type.
  Variable Expr_expr : Expr typD expr.

  Variable FI_Emp : FuncInstance0 typD expr emp.

  Variable SA_Star : SymAppN (n := 0) ((fun _ => tySep) :: (fun _ => tySep) :: nil)
                                      tySep.
  Variable SA_Inj : SymAppN (n := 0) ((fun _ => tyProp) :: nil)
                                      tySep.
  Variable SA_Ex : SymAppN (n := 1) ((fun _ => tySep) :: nil) (fun _ => tySep).

  Section cases.
    Variable R : Type.
    Variable e : expr.
    Hypothesis caseEmp : unit -> R.
    Hypothesis caseInj : forall l, acc l e -> R.
    Hypothesis caseStar : forall l r : expr, acc l e -> acc r e -> R.
    Hypothesis caseEx : typ -> forall b : expr, acc b e -> R.
    Hypothesis caseElse : expr -> R.

    Definition matchSepLog : R.
      refine (
          match sappn_check SA_Star e with
            | Some (existT (_,es) accs) =>
              caseStar (vector_hd es) (vector_hd (vector_tl es))
                       (ForallV_vector_hd accs) (ForallV_vector_hd (ForallV_vector_tl accs))
            | None =>
              match sappn_check SA_Inj e with
                | Some (existT (_,es) accs) =>
                  caseInj (vector_hd es)
                          (ForallV_vector_hd accs)
                | None =>
                  match sappn_check SA_Ex e with
                    | Some (existT (ts,es) accs) =>
                      caseEx (vector_hd ts) (vector_hd es)
                             (ForallV_vector_hd accs)
                    | None =>
                      ctor0_match (fun _ => R)
                                  caseEmp
                                  caseElse
                                  e
                  end
              end
          end
        ).
    Defined.
  End cases.
End syntax.
