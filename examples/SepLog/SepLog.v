Require Import Examples.SepLog.NatDed.

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

  Delimit Scope logic_scope with logic.

  Notation "'ALL' x .. y => P" :=
    (All (fun x => .. (All (fun y => P)) .. ))
      (x closed binder, y closed binder, at level 100, P at next level) : logic_scope.

  Notation "'EX' x .. y => P" :=
    (Ex (fun x => .. (Ex (fun y => P)) .. ))
      (x closed binder, y closed binder, at level 100, P at next level) : logic_scope.

  Open Local Scope logic_scope.

  Class SeparationLogic_Laws : Type :=
  { himp_trans : Entails (Logic := Logic_L) (@Tr L _)
                         (ALL p q r =>
                          Impl (himp p q) (Impl (himp q r) (himp p r)))
  ; star_emp_p : Entails (Logic := Logic_L) (@Tr L _) (ALL p => himp (star p emp) p)
  ; star_emp_c : Entails (Logic := Logic_L) (@Tr L _) (ALL p => himp p (star p emp))
  ; star_comm : Entails (Logic := Logic_L) (@Tr L _) (ALL p q => himp (star p q) (star q p))
  ; star_assoc : Entails (Logic := Logic_L) (@Tr L _) (ALL p q r =>
       himp (star (star p q) r) (star p (star q r)))
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

  Section fold.
    Variable R : Type.
    Variable caseEmp : R.
    Variable caseInj : expr -> R.
    Variable caseStar : R -> R -> R.
    Variable caseEx : typ -> R -> R.
    Variable caseElse : expr -> R.

    Definition foldSepLog (e : expr) : R.
      refine (
          @Fix_F expr (@acc _ _ _ Expr_expr) (fun _ => R)
                 (fun e recur =>
                    matchSepLog e
                                (fun _ => caseEmp)
                                (fun P _ => caseInj P)
                                (fun l r lacc racc =>
                                   let lr := recur l lacc in
                                   let rr := recur r racc in
                                   caseStar lr rr)
                                (fun t b bacc =>
                                   caseEx t (recur b bacc))
                                (fun _ => caseElse e))
                 e (wf_acc e)).
    Defined.
  End fold.
End syntax.
