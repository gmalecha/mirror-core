Require Import ExtLib.Structures.Logic.

Set Implicit Arguments.
Set Strict Implicit.

Section sl.
  Variable L P : Type.

  Class SeparationLogic : Type :=
  { emp : P
  ; star : P -> P -> P
  ; inj  : L -> P
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

Require Import MirrorCore.Repr.
Require Import MirrorCore.Expr.

Section syntax.

  Variable L S : Type.
  Variable SL : SeparationLogic L S.
  Variable QSL : Quant S.

  Definition sl_types : Repr type := 
    listToRepr (default_type L :: default_type S :: nil) (empty_type).
  Definition sl_funcs ts : Repr (function (repr sl_types ts)) :=
    let ts := repr sl_types ts in
    let s := tvType 1 in
    let l := tvType 0 in
    listToRepr (F ts 0 s (@emp _ _ SL) ::
                F ts 0 (tvArr s (tvArr s s)) (@star _ _ SL) ::
                F ts 0 (tvArr l s) (@inj _ _ SL) ::
                F ts 1 (tvArr (tvArr (tvVar 0) s) s) (@Ex _ _) ::
                nil) (F ts 0 tvProp False).

  Section cases.
    Variable ts : types.
    Variable R : Type.
    Hypothesis caseEmp : unit -> R.
    Hypothesis caseStar : expr (repr sl_types ts) -> expr (repr sl_types ts) -> R.
    Hypothesis caseInj : expr (repr sl_types ts) -> R.
    Hypothesis caseEx : typ -> expr (repr sl_types ts) -> R.
    Hypothesis default : expr (repr sl_types ts) -> R.

    Definition matchSepLog (e : expr (repr sl_types ts)) : R :=
      match e with
        | Func 0 nil => caseEmp tt
        | App (Func 1 nil) (l :: r :: nil) => caseStar l r
        | App (App (Func 1 nil) (l :: nil)) (r :: nil) => caseStar l r
        | App (Func 2 nil) (e :: nil) => caseInj e
        | App (Func 3 (t :: nil)) (Abs _ e :: nil) => caseEx t e
        | e => default e
      end.

    Theorem matchSepLog_sem : forall fs',
                                let fs := repr (sl_funcs ts) fs' in 
                                forall (P : _ -> Prop) u g e,
      (P (default e)) ->
      (@exprD _ fs u g e (tvType 1) = Some (@emp _ _ _) -> P (caseEmp tt)) ->
      (forall pe qe p q, 
         @exprD _ fs u g pe (tvType 1) = Some p ->
         @exprD _ fs u g qe (tvType 1) = Some q ->
         @exprD _ fs u g e (tvType 1) = Some (@star _ _ _ p q) -> P (caseStar pe qe)) ->
      WellTyped_expr (typeof_funcs fs) (typeof_env u) (typeof_env g) e (tvType 1) ->
      P (matchSepLog e).
    Proof.
      intros. unfold matchSepLog.
      repeat (solve [ auto ] || 
              match goal with
                | [ |- P match ?X with _ => _ end ] =>
                  destruct X; simpl in *; auto
              end).
      { eapply H0. unfold exprD. simpl. destruct (split_env g); auto. }
      { clear H0 H. unfold exprD in H1. simpl in H1.
        Ltac inversions :=
          repeat match goal with
                   | [ H : WellTyped_expr _ _ _ _ _ |- _ ] =>
                     apply WellTyped_expr_App in H ||
                     apply WellTyped_expr_Const in H ||
                     apply WellTyped_expr_Var in H ||
                     apply WellTyped_expr_UVar in H ||
                     apply WellTyped_expr_Func in H
                   | [ H : exists x, _ |- _ ] =>
                     destruct H
                   | [ H : _ /\ _ |- _ ] => destruct H
                   | [ H : Forall2 _ _ _ |- _ ] => inversion H; clear H; subst
                 end.
        inversions. simpl in *. inversion H; clear H; subst; simpl in *.
        destruct y; try congruence. destruct n; try congruence. destruct n; try congruence.
        destruct y0; try congruence. destruct n; try congruence. destruct n; try congruence.
        unfold typeof_func in *; simpl in *.
        SearchAbout WellTyped_expr.
        

  End cases.
End syntax.