(* RtacDemo.v
 * Contains a demonstration of the quantifier-puller's funcionality,
 * As well as some supporting infrastructure/automation.
 *)

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
Require Import McExamples.PolyRewrite.MSimple.
Require Import McExamples.PolyRewrite.MSimpleReify.
Require Import McExamples.PolyRewrite.QuantifierPuller.PolyQuantPullRtac.

Set Implicit Arguments.
Set Strict Implicit.

(* Convenient abbreviation for modular type *)
Let tyBNat := CoreTypes.tyBase0 tyNat.

Definition fAnd a b : expr typ func := App (App (Inj MSimple.And) a) b.
Definition fOr a b : expr typ func := App (App (Inj MSimple.And) a) b.
Definition fAll t P : expr typ func := App (Inj (MSimple.All t)) (Abs t P).
Definition fEx t P : expr typ func := App (Inj (MSimple.Ex t)) (Abs t P).
Definition fEq t : expr typ func := (Inj (MSimple.Eq t)).
Definition fImpl : expr typ func := (Inj MSimple.Impl).
Definition fEq_nat a b : expr typ func := App (App (fEq tyBNat) a) b.
Definition fN n : expr typ func := Inj (MSimple.N n).

Fixpoint goal n : expr typ func :=
  match n with
  | 0 => fEq_nat (fN 0) (fN 0)
  | S n =>
    fAnd (fEx tyBNat (goal n)) (fEx tyBNat (goal n))
  end.


Fixpoint goal2 mx n (acc : nat) : expr typ func :=
  match n with
  | 0 =>
    if acc ?[ lt ] mx then
      fEx tyBNat (fEq_nat (fN 0) (fN 0))
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

Fixpoint goal2_D' mx mx2 n (acc : nat) : Prop :=
  match n with
  | 0 =>
    if acc ?[ lt ] mx then
      exists x : nat, 0 = 0
    else if acc ?[lt] mx2 then
           exists b : bool, 0 = 0 else
           0 = 0
  | S n =>
    goal2_D' mx mx2 n (acc * 2) /\ goal2_D' mx mx2 n (acc * 2 + 1)
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
Require Import MirrorCore.CTypes.CoreTypes.

Instance Expr_expr : Expr typ (expr typ func) := Expr.Expr_expr.

Ltac reduce_propD g e := eval cbv beta iota zeta delta
    [ g goalD Ctx.propD exprD_typ0 exprD Expr_expr Expr.Expr_expr
      exprT_UseV exprT_UseU exprT_GetUAs exprT_GetVAs
      HList.nth_error_get_hlist_nth HList.hlist_hd HList.hlist_tl
      ExprDsimul.ExprDenote.lambda_exprD func_simul symAs typ0_cast Typ0_Prop
      typeof_sym RSym_func type_cast typeof_func RType_ctyp typ2_match
      Typ2_Fun ctyp_dec
      ctyp_dec
      typ2 Relim exprT_Inj eq_ind eq_rect eq_rec
      AbsAppI.exprT_App eq_sym
      typ2_cast sumbool_rec sumbool_rect eq_ind_r f_equal typ0 symD funcD
      RType_typ symbol_dec ctyp_cast TSym_typ' typ'_dec
      typD ctypD symbolD
    ] in e.

Arguments Typ0_Prop {_ _}.

(* Maybe we can use typeclasses to resolve the reification function *)
  Ltac run_tactic reify tac tac_sound :=
    match goal with
    | |- ?goal =>
      let k g :=
          let result := constr:(runRtac typ (expr typ func) nil nil g tac) in
          let resultV := eval vm_compute in result in
          lazymatch resultV with
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
            lazymatch post with
            | ?G =>
              cut G ;
                [ change (@closedD _ _ _ Typ0_Prop Expr_expr nil nil g g'V) ;
                  cut (result = More_ (@TopSubst _ _ _ _) g'V) ;
                  [ exact (@rtac_More_closed_soundness _ _ _ _ _ _ tac_sound nil nil g g'V)
                  | vm_cast_no_check (@eq_refl _ resultV) ]
                | try clear g'V g ]
            end
          | Fail => idtac "failed"
          | ?G => fail "reduction failed with " G
          end
      in
      reify_expr_bind reify k [[ True ]] [[ goal ]]
    end.

  Definition goal2_D'' n : Prop :=
  let thirdn := Nat.div n 3 in
  goal2_D' thirdn (2 * thirdn) n 0.

(*Set Printing Depth 5.*) (* To avoid printing large terms *)

Ltac the_tac := run_tactic reify_simple rewrite_it rewrite_it_sound.

(* examples of things that don't work *)
(*
Goal ((exists (x : nat), 1 = 1)/\(exists (y : nat), 2 = 2)).
Variable k : nat.
Goal (1 = 1 /\ exists (y : nat), y = 1).
  Time the_tac.
 *)

Goal (exists x : nat, x = 1) /\ (1 = 1).
  Time the_tac.
  repeat exists 1. tauto.
Qed.

Goal goal2_D'' 2.
  vm_compute. Time the_tac.
  repeat exists 0.
repeat exists true. tauto.
Qed.

(* Data: keeping track of values for runs for different n
   we report time-out if any runs time out

   we report (total, reification) times as pairs

   TODO: we should also report QED times

   we need at least 3-14
   3: .034, .032, .032, .032, .032 (reif 0 for all)
   4: .042, .043, .043, .043, .043 (reif 0 for all)
   5: (.062, 0), (.069, .004), (.062, 0), (.062, 0), (.063, 0)
   6: (.111, .004), (.115, .004), (.113, 0), (.113, 0), (.115, 0)
   7: ?
   8: (.371, .004), (.372, .004), (.372, .004), (.372, .004), (.373, .008)
   9: ?
   10: (1.602, .016), (1.749, .012), (1.651, .016), (1.633, .016), (1.65, .016)
   12: (7.123, .06), (7.08, .052), (7.02, .056), (6.977, .056), (6.98, .056)
   13: ?
   14: (28.662, .276), (30.69, .264), (28.595, .272), (,), (,)
   16:
*)


(* original goal *)
Goal goal2_D' 2 4 (* n = *) 5 0.
  simpl.
(*
  Check ex.

  Ltac reify_term e :=
    lazymatch e with
    | fun ctx => fst ctx => uconstr:(Var 0)
    | fun ctx => snd (@?V ctx) => get_var V uconstr:(1)
    | fun ctx => @?X ctx /\ @?Y ctx =>
      let x := reify_term X in
      let y := reify_term Y in
      uconstr:(fAnd x y)
    | fun ctx => @eq ?ty (@?l ctx) (@?r ctx) =>
      let ty := reify_type ty in
      let l := reify_term l in
      let r := reify_term r in
      uconstr:(App (App (fEq ty) l) r)
    | fun ctx => @ex ?ty (@?P ctx) =>
      let ty := reify_type ty in
      let P := reify_term P in
      uconstr:(fEx ty P)
    | fun ctx => (fun x : ?ty => @?P ctx x) =>
      let ty := reify_type ty in
      let P := constr:(fun ctx => P (snd ctx) (fst ctx)) in
      let P := reify_term P in
      uconstr:(Abs ty P)
    | fun ctx => O =>
      uconstr:(fN 0)
    end
  with get_var v acc :=
    lazymatch v with
    | fun ctx => fst ctx => uconstr:(Var acc)
    | fun ctx => snd (@?X ctx) => let acc' := uconstr:(S acc) in
                                  get_var X acc'
    end
  with reify_type t :=
    lazymatch t with
    | nat => tyBNat
    end.

  Goal (fun x : nat => x) = fun x => x.
    match goal with
    | |- ?X => let x := reify_term (fun ctx : unit => (fun x : nat => x)) in
               pose x
    end.
*)



Time run_tactic reify_simple rewrite_it rewrite_it_sound.
repeat exists 0.
repeat exists true. tauto.
Qed.

Module Demo.
  Ltac prep := vm_compute.
  Ltac run := run_tactic reify_simple rewrite_it rewrite_it_sound.
  Ltac cleanup := repeat ( first [exists 0 | exists true]); tauto.
  Definition goal := goal2_D''.
End Demo.
