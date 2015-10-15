Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Reify.Reify.
Require Import McExamples.Cancel.MonoidSyntax.
Require Import McExamples.Cancel.CancelTacNoMatch.

Set Implicit Arguments.
Set Strict Implicit.

Reify BuildLemma < reify_monoid_typ reify_monoid reify_monoid >
      lem_refl : Monoid.refl.

Definition the_tactic fs :=
  @CancelTacNoMatch.cancel typ func RType_typ _ _ (RSym_func fs)
                           tyM (known mR) (known mP) (known mU)
                           (@EAPPLY typ func RType_typ Typ0_tyProp Typ2_tyArr (RSym_func fs) lem_refl).

Definition the_Expr fs := (@Expr.Expr_expr typ func _ _ (RSym_func fs)).

Theorem sound_tac : forall fs,
    @rtac_sound typ (expr typ func) RType_typ Typ0_tyProp
                 (the_Expr fs) (the_tactic fs).
Proof.
  intros. eapply CancelTacNoMatch.cancel_sound; eauto with typeclass_instances.
  constructor; exact Monoid.plus_unit_c.
  constructor; exact Monoid.plus_assoc_c1.
  constructor; exact Monoid.plus_assoc_c2.
  constructor; exact Monoid.plus_comm_c.
  constructor; exact Monoid.plus_cancel.
  constructor; exact Monoid.plus_unit_p.
  constructor; exact Monoid.plus_assoc_p1.
  constructor; exact Monoid.plus_assoc_p2.
  constructor; exact Monoid.plus_comm_p.
  eapply RtacSound_EAPPLY; eauto with typeclass_instances.
  constructor; compute; exact Monoid.refl.
Qed.

Ltac rtac_canceler :=
  lazymatch goal with
  | |- ?trm =>
    let k tbl e :=
      let result := constr:(@Interface.runRtac typ (expr typ func) nil nil e (the_tactic tbl)) in
      let resultV := eval vm_compute in result in
      match resultV with
        | Solved _ =>
          change (@Interface.propD _ _ _ Typ0_tyProp (the_Expr tbl) nil nil e) ;
          cut (result = resultV) ;
            [ set (pf := @Interface.rtac_Solved_closed_soundness
                       _ _ _ _ _ _ (sound_tac tbl)
                       nil nil e) ;
              exact pf
            | vm_cast_no_check (@eq_refl _ resultV) ]
      end
    in
    reify_expr_bind
      reify_monoid k
      [[ (fun x : @mk_dvar_map _ _ _ typD table_terms (@SymEnv.F typ _) => True) ]]
      [[ trm ]]
  end.

Goal Monoid.goal 120.
  Monoid.prep.
  Time rtac_canceler.
Time Qed.
