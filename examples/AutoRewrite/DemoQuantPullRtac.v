Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.Compat.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprD.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.RewriteStrat.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.RTac.IdtacK.
Require Import McExamples.Simple.Simple.
Require Import McExamples.Simple.SimpleReify.
Require Import McExamples.AutoRewrite.QuantPullRtac.

Set Implicit Arguments.
Set Strict Implicit.

Definition fAnd a b : expr typ func := App (App (Inj Simple.And) a) b.
Definition fOr a b : expr typ func := App (App (Inj Simple.And) a) b.
Definition fAll t P : expr typ func := App (Inj (Simple.All t)) (Abs t P).
Definition fEx t P : expr typ func := App (Inj (Simple.Ex t)) (Abs t P).
Definition fEq t : expr typ func := (Inj (Simple.Eq t)).
Definition fImpl : expr typ func := (Inj Simple.Impl).
Definition fEq_nat a b : expr typ func := App (App (fEq tyNat) a) b.
Definition fN n : expr typ func := Inj (Simple.N n).

Fixpoint goal n : expr typ func :=
  match n with
  | 0 => fEq_nat (fN 0) (fN 0)
  | S n =>
    fAnd (fEx tyNat (goal n)) (fEx tyNat (goal n))
  end.


Fixpoint goal2 mx n (acc : nat) : expr typ func :=
  match n with
  | 0 =>
    if acc ?[ lt ] mx then
      fEx tyNat (fEq_nat (fN 0) (fN 0))
    else
      fEq_nat (fN 0) (fN 0)
  | S n =>
    fAnd (goal2 mx n (acc * 2)) (goal2 mx n (acc * 2 + 1)) (*
    fAnd (fEx tyNat (goal n)) (fEx tyNat (goal n)) *)
  end.

Fixpoint goal2_D mx n (acc : nat) : Prop :=
  match n with
  | 0 =>
    if acc ?[ lt ] mx then
      exists x : nat, 0 = 0
    else
      0 = 0
  | S n =>
    goal2_D mx n (acc * 2) /\ goal2_D mx n (acc * 2 + 1)
  end.


Fixpoint count_quant (e : expr typ func) : nat :=
  match e with
  | App (Inj (Ex _)) (Abs _ e') => S (count_quant e')
  | _ => 0
  end.

Definition benchmark (n m : nat) : bool :=
  match quant_pull (goal2 m n 0) (Rinj fImpl) nil (TopSubst _ nil nil)
  with
  | Some _ => true
  | _ => false
  end.

Definition rewrite_it : rtac typ (expr typ func) :=
  @auto_setoid_rewrite_bu typ func (expr typ func)
                          (Rflip (Rinj fImpl))
                          (is_reflR is_refl) (is_transR is_trans) pull_all_quant get_respectful.
Theorem rewrite_it_sound : rtac_sound rewrite_it.
Proof.
  eapply auto_setoid_rewrite_bu_sound with (RbaseD:=RbaseD).
  - eapply RbaseD_single_type.
  - reflexivity.
  - eapply is_reflROk; eapply is_refl_ok.
  - eapply is_transROk; eapply is_trans_ok.
  - eapply pull_all_quant_sound.
  - eapply get_respectful_sound.
Qed.

Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.Lambda.Expr.

Instance Expr_expr : Expr typ (expr typ func) := Expr.Expr_expr.

Ltac reduce_propD g e := eval cbv beta iota zeta delta
    [ g goalD Ctx.propD exprD_typ0 exprD Expr_expr Expr.Expr_expr
      ExprDsimul.ExprDenote.lambda_exprD func_simul symAs typ0_cast Typ0_Prop
      typeof_sym RSym_func type_cast typeof_func RType_typ typ2_match
      Typ2_tyArr typ_eq_dec  typ_rec typ_rect
      typ2 Relim exprT_Inj eq_ind eq_rect eq_rec
      AbsAppI.exprT_App eq_sym
      typ2_cast sumbool_rec sumbool_rect eq_ind_r f_equal typ0 symD funcD
    ] in e.

  Ltac run_tactic reify tac tac_sound :=
    match goal with
    | |- ?goal =>
      let k g :=
          let result := constr:(runRtac typ (expr typ func) nil nil g tac) in
          let resultV := eval vm_compute in result in
          match resultV with
          | Solved _ =>
            change (@propD _ _ _ Typ0_Prop Expr_expr nil nil g) ;
              cut(result = resultV) ;
              [
              | vm_cast_no_check (@eq_refl _ resultV) ]
          | More_ _ ?g' =>
            pose (g'V := g') ;
            let post := constr:(match @goalD _ _ _ Typ0_Prop Expr_expr nil nil g'V with
                                | Some G => G HList.Hnil HList.Hnil
                                | None => True
                                end) in
            let post := reduce_propD g'V post in
            match post with
            | ?G =>
              cut G ;
                [ change (@closedD _ _ _ Typ0_Prop Expr_expr nil nil g g'V) ;
                  cut (result = More_ (@TopSubst _ _ _ _) g'V) ;
                  [ exact (@rtac_More_closed_soundness _ _ _ _ _ _ tac_sound nil nil g g'V)
                  | vm_cast_no_check (@eq_refl _ resultV) ]
                | try clear g'V g ]
            end
          | Fail => idtac "failed"
          end
      in
      reify_expr_bind reify k [[ True ]] [[ goal ]]
    end.

Goal goal2_D 10 7 0.
simpl.
Time run_tactic reify_simple rewrite_it rewrite_it_sound.
repeat exists 0; tauto.
Qed.
