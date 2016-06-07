(* DemoPolyQuantPullRtac.v
 * Contains some supporting infrastructure/automation for MSimple
 * Similar to DemoPolyQuantPullRtac; generic things need to be factored out
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
Require Import McExamples.PolyRewrite.MSimpleMonads.
Require Import McExamples.PolyRewrite.MSimpleMonadsReify.

(* for examples *)
Require Import McExamples.PolyRewrite.Monads.

Set Implicit Arguments.
Set Strict Implicit.

(* Convenient abbreviation for modular type *)
Let tyBNat := ModularTypes.tyBase0 tyNat.

Definition fAnd a b : expr typ func := App (App (Inj MSimpleMonads.And) a) b.
Definition fOr a b : expr typ func := App (App (Inj MSimpleMonads.And) a) b.
Definition fAll t P : expr typ func := App (Inj (MSimpleMonads.All t)) (Abs t P).
Definition fEx t P : expr typ func := App (Inj (MSimpleMonads.Ex t)) (Abs t P).
Definition fEq t : expr typ func := (Inj (MSimpleMonads.Eq t)).
Definition fImpl : expr typ func := (Inj MSimpleMonads.Impl).
Definition fEq_nat a b : expr typ func := App (App (fEq tyBNat) a) b.
Definition fN n : expr typ func := Inj (MSimpleMonads.N n).

Lemma OptionOk : MonadLaws option OptionMonad.Monad_option.
Proof.
  constructor; simpl; [reflexivity| intros m m'; destruct m'; reflexivity |].
  intros.
  destruct m; [|reflexivity].
  destruct (f a); reflexivity.
Qed.

Require Import MirrorCore.Lambda.Polymorphic.

Let Rbase := expr typ func.

SearchAbout Monad.Monad option.

Definition law1 := lem1 option _ OptionOk.
Definition law2 := lem2 option _ OptionOk.
Definition law3 := lem3 option _ OptionOk.

Check law1.
Print Lemma.

Definition rlaw1 : polymorphic typ 2 (Lemma.lemma typ (expr typ func) (rw_concl typ func Rbase)) :=
  Eval unfold Lemma.add_var, Lemma.add_prem, Lemma.vars, Lemma.concl, Lemma.premises, Lemma.foralls in
    <:: @law1 ::>.

Definition law2 := lem2 option _ OptionOk.
Definition law3 := lem3 option _ OptionOk.

Require Import MirrorCore.Lambda.Rewrite.HintDbs.

Definition get_respectful : ResolveProper typ func Rbase :=
  do_prespectful

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
Require Import MirrorCore.MTypes.ModularTypes.

Instance Expr_expr : Expr typ (expr typ func) := Expr.Expr_expr.
Locate Typ2_tyArr.

Ltac reduce_propD g e := eval cbv beta iota zeta delta
    [ g goalD Ctx.propD exprD_typ0 exprD Expr_expr Expr.Expr_expr
      ExprDsimul.ExprDenote.lambda_exprD func_simul symAs typ0_cast Typ0_Prop
      typeof_sym RSym_func type_cast typeof_func RType_mtyp typ2_match
      Typ2_Fun mtyp_dec
      mtyp_dec
      typ2 Relim exprT_Inj eq_ind eq_rect eq_rec
      AbsAppI.exprT_App eq_sym
      typ2_cast sumbool_rec sumbool_rect eq_ind_r f_equal typ0 symD funcD
      RType_typ symbol_dec mtyp_cast TSym_typ' typ'_dec
      typD mtypD symbolD
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
          | ?G => fail "reduction failed with " G
          end
      in
      reify_expr_bind reify k [[ True ]] [[ goal ]]
    end.

Goal goal2_D' 2 4 5 0.
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

Require Import MirrorCore.Lambda.ExprCore.
Definition rei_ex1 : expr typ func.
                       let k := eval red in ex1 in
                           reify k.
Defined.
