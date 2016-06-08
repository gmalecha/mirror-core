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
Require Import MirrorCore.Lambda.RewriteRelations.
Require Import MirrorCore.Lambda.RewriteStrat.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.RTac.IdtacK.
Require Import MirrorCore.Lambda.Rewrite.HintDbs.
Require Import MirrorCore.MTypes.ModularTypes.
Require Import MirrorCore.Polymorphic.
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

Let Rbase := expr typ func.

Definition law1 := lem1 option _ OptionOk.
Definition law2 := lem2 option _ OptionOk.
Definition law3 := lem3 option _ OptionOk.

Existing Instance Reify_polymorphic.

Instance RType_typ_opt : RType typ := RType_typ option.
Existing Instance Expr.Expr_expr.
Existing Instance Typ2_Fun.
Existing Instance Typ2Ok_Fun.

Instance Reify_simple_type_opt : Reify typ := Reify_simple_type option.
Instance Reify_expr_simple_opt : Reify (expr typ func) := Reify_expr_simple option.

Instance RSym_func_opt : RSym func := @RSym_func option OptionMonad.Monad_option.
Instance RSymOk_func_opt : RSymOk RSym_func_opt := @RSymOk_func option OptionMonad.Monad_option.

Definition rlaw1 : polymorphic typ 2 (Lemma.lemma typ (expr typ func) (rw_concl typ func Rbase)) :=
  Eval unfold Lemma.add_var, Lemma.add_prem, Lemma.vars, Lemma.concl, Lemma.premises, Lemma.foralls in
    <:: @law1 ::>.

Definition rlaw2 : polymorphic typ 1 (Lemma.lemma typ (expr typ func) (rw_concl typ func Rbase)) :=
  Eval unfold Lemma.add_var, Lemma.add_prem, Lemma.vars, Lemma.concl, Lemma.premises, Lemma.foralls in
    <:: @law2 ::>.

Definition rlaw3 : polymorphic typ 3 (Lemma.lemma typ (expr typ func) (rw_concl typ func Rbase)) :=
  Eval unfold Lemma.add_var, Lemma.add_prem, Lemma.vars, Lemma.concl, Lemma.premises, Lemma.foralls in
    <:: @law3 ::>.

Definition the_lemmas : RewriteHintDb Rbase :=
  @PRw _ _ _ 2 rlaw1 IDTACK ::
       @PRw _ _ _ 1 rlaw2 IDTACK ::
       @PRw _ _ _ 3 rlaw3 IDTACK ::
       nil.

(* Copied from PolyQuantPullRtac; they really should be abstracted to minimize this repetition. *)
Definition RbaseD (e : expr typ func) (t : typ)
  : option (TypesI.typD t -> TypesI.typD t -> Prop) :=
  @env_exprD typ RType_typ_opt (expr typ func) Expr.Expr_expr nil nil (tyArr t (tyArr t tyProp)) e.

Theorem RbaseD_single_type
: forall (r : expr typ func) (t1 t2 : typ)
         (rD1 : TypesI.typD t1 -> TypesI.typD t1 -> Prop)
         (rD2 : TypesI.typD t2 -> TypesI.typD t2 -> Prop),
    RbaseD r t1 = Some rD1 -> RbaseD r t2 = Some rD2 -> t1 = t2.
Proof.
  unfold RbaseD, env_exprD. simpl; intros.
  forward.
  generalize (lambda_exprD_deterministic _ _ _ H0 H). unfold Rty.
  intros. inversion H3. reflexivity.
Qed.

Ltac polymorphicD_intro :=
  try lazymatch goal with
    | |- @polymorphicD _ _ _ O _ =>
      red
    | |- @polymorphicD _ _ _ (S _) _ => intro ; polymorphicD_intro
    end.

Ltac get_num_arrs t :=
  lazymatch t with
  | _ -> ?T => let x := get_num_arrs T in
               constr:(S x)
  | _ => constr:(0)
  end.

Ltac reduce_exprT :=
  repeat progress (red; simpl; repeat rewrite mtyp_cast_refl);
  unfold AbsAppI.exprT_App, exprT_Inj, Rcast_val, Rcast, Relim, Rsym; simpl.

Ltac prove_lem lem :=
  polymorphicD_intro ;
  red; intros;
  reduce_exprT ;
  try first [ exact lem
            | exact (lem _)
            | exact (lem _ _)
            | exact (lem _ _ _)
            | exact (lem _ _ _ _)
            | exact (lem _ _ _ _ _)
            | exact (lem _ _ _ _ _ _)
            ].

Lemma rlaw1_sound
: polymorphicD (Lemma.lemmaD (rw_conclD RbaseD) nil nil) (n:=2) rlaw1.
Proof. prove_lem law1. Defined.

Lemma rlaw2_sound
: polymorphicD (Lemma.lemmaD (rw_conclD RbaseD) nil nil) (n:=1) rlaw2.
Proof. prove_lem law2. Defined.

Lemma rlaw3_sound
: polymorphicD (Lemma.lemmaD (rw_conclD RbaseD) nil nil) (n:=3) rlaw3.
Proof. prove_lem law3. Defined.

Theorem the_lemmas_sound : RewriteHintDbOk RbaseD the_lemmas.
Proof.
  repeat first [ apply Forall_cons | apply Forall_nil ]; split; try apply IDTACK_sound.
  { unfold polymorphicD. intros.
    apply rlaw1_sound. }
  { unfold polymorphicD. intros. apply rlaw2_sound. }
  { unfold polymorphicD. intros. apply rlaw3_sound. }
Qed.

Require Import MirrorCore.Lambda.Rewrite.HintDbs.

Existing Instance RelDec_eq_mtyp.

Definition my_expr_acc := @expr_acc typ func.
Instance TSym_typ'_opt : TSym typ':= TSym_typ' option.

Check RelDec_eq_func.

Instance RelDec_eq_func_opt : RelDec eq := RelDec_eq_func option.

Definition get_respectful : ResolveProper typ func Rbase :=
  @do_prespectful typ func RType_typ_opt RSym_func_opt (RelDec_eq_mtyp typ' (TSym_typ' option)) Rbase (rel_dec (equ := eq) (RelDec := RelDec_eq_expr (RelDec_eq_mtyp typ' _) (RelDec_eq_func_opt))) (MTypeUnify.mtype_unify typ') (@tyVar typ') nil.

Definition is_trans : trans_dec Rbase :=
  fun r =>
    match r with
    | Inj (Eq _)
    | Inj Lt
    | Inj Impl => true
    | _ => false
    end.

Definition is_refl : refl_dec Rbase :=
  fun (r : Rbase) =>
    match r with
    | Inj (Eq _)
    | Inj Impl => true
    | _ => false
    end.

Definition simple_reduce (e : expr typ func) : expr typ func :=
  run_ptrn
    (pmap (fun abcd => let '(a,(b,(c,d),e)) := abcd in
                       App a (Abs c (App (App b d) e)))
          (app get (abs get (fun t =>
                               app (app get
                                        (pmap (fun x => (t,Red.beta x)) get))
                                   (pmap Red.beta get)))))
    e e.

Theorem is_refl_ok : refl_dec_ok RbaseD is_refl.
Proof.
  red.
  destruct r; simpl; try congruence.
  destruct f; simpl; try congruence.
  { unfold RbaseD; simpl.
    unfold env_exprD. simpl. intros.
    autorewrite with exprD_rw in H0.
    forward. inv_all; subst.
    unfold symAs in H0. unfold typeof_sym in H0.
    unfold RSym_func_opt, RSym_func in H0.
    unfold typeof_func in H0.
    forward. inv_all. subst. simpl.
    clear. red in r. inversion r.
    subst.
    rewrite (UIP_refl r). compute. reflexivity. }
  { unfold RbaseD; simpl.
    unfold env_exprD. simpl. intros.
    autorewrite with exprD_rw in H0.
    forward. inv_all; subst.
    unfold symAs in H0. unfold typeof_sym in H0.
    unfold RSym_func_opt, RSym_func in H0.
    unfold typeof_func in H0.
    forward. inv_all. subst. simpl.
    clear. red in r. inversion r.
    subst.
    rewrite (UIP_refl r). compute. intros; tauto. }
  Unshelve.
  exact option.
  exact option.
Qed.

Theorem is_trans_ok : trans_dec_ok RbaseD is_trans.
Proof.
  red.
  destruct r; simpl; try congruence.
  destruct f; simpl; try congruence.
  { unfold RbaseD; simpl.
    unfold env_exprD. simpl. intros.
    autorewrite with exprD_rw in H0.
    forward. inv_all; subst.
    unfold symAs in H0. unfold typeof_sym in H0.
    unfold RSym_func_opt, RSym_func in H0.
    unfold typeof_func in H0.
    forward. }
  { unfold RbaseD; simpl.
    unfold env_exprD. simpl. intros.
    autorewrite with exprD_rw in H0.
    forward. inv_all; subst.
    unfold symAs in H0. unfold typeof_sym in H0.
    unfold RSym_func_opt, RSym_func in H0.
    unfold typeof_func in H0.
    forward. inv_all. subst.
    simpl. clear. inversion r.
    subst. rewrite (UIP_refl r). compute. congruence. }
  { unfold RbaseD; simpl.
    unfold env_exprD. simpl. intros.
    autorewrite with exprD_rw in H0.
    forward. inv_all; subst.
    unfold symAs in H0. unfold typeof_sym in H0.
    unfold RSym_func_opt, RSym_func in H0.
    unfold typeof_func in H0.
    forward. inv_all. subst.
    clear. inversion r. subst.
    rewrite (UIP_refl r).
    compute. tauto. }
  Unshelve.
  exact option.
  exact option.
Qed.

Definition the_rewrites (lems : RewriteHintDb Rbase)
  : RwAction typ func Rbase :=
  rw_post_simplify simple_reduce (rw_simplify Red.beta (using_prewrite_db rel_dec (CompileHints lems))).

Definition monad_simplify : RwAction typ func Rbase :=
  repeat_rewrite (fun e r =>
                    bottom_up (is_reflR is_refl) (is_transR is_trans) (the_rewrites the_lemmas)
                              get_respectful e r)
                 (is_reflR is_refl) (is_transR is_trans) false 300.

Lemma simple_reduce_sound :
  forall (tus tvs : tenv typ) (t : typ) (e : expr typ func)
         (eD : exprT tus tvs (TypesI.typD t)),
    ExprDsimul.ExprDenote.lambda_exprD tus tvs t e = Some eD ->
    exists eD' : exprT tus tvs (TypesI.typD t),
      ExprDsimul.ExprDenote.lambda_exprD tus tvs t (simple_reduce e) = Some eD' /\
      (forall (us : HList.hlist TypesI.typD tus)
              (vs : HList.hlist TypesI.typD tvs), eD us vs = eD' us vs).
Proof.
  unfold simple_reduce.
  intros.
  revert H.
  eapply Ptrns.run_ptrn_sound.
  { repeat first [ simple eapply ptrn_ok_pmap
                 | simple eapply ptrn_ok_app
                 | simple eapply ptrn_ok_abs; intros
                 | simple eapply ptrn_ok_get
                 ]. }
  { do 3 red. intros; subst.
    reflexivity. }
  { intros. ptrnE.
    eapply lambda_exprD_Abs_prem in H; forward_reason; subst.
    inv_all. subst.
    generalize (Red.beta_sound tus (x4 :: tvs) x10 x6).
    generalize (Red.beta_sound tus (x4 :: tvs) x7 x).
    simpl.
    change_rewrite H1. change_rewrite H2.
    intros; forward.
    erewrite lambda_exprD_App; try eassumption.
    2: erewrite lambda_exprD_Abs; try eauto with typeclass_instances.
    2: rewrite typ2_match_iota; eauto with typeclass_instances.
    2: rewrite type_cast_refl; eauto with typeclass_instances.
    2: erewrite lambda_exprD_App; try eassumption.
    3: erewrite lambda_exprD_App; try eassumption; eauto.
    2: autorewrite_with_eq_rw; reflexivity.
    simpl. eexists; split; eauto.
    unfold AbsAppI.exprT_App, AbsAppI.exprT_Abs. simpl.
    intros. unfold Rrefl, Rcast_val, Rcast, Relim; simpl.
    f_equal.
    apply FunctionalExtensionality.functional_extensionality.
    intros. rewrite H5. rewrite H6. reflexivity. }
  { eauto. }
Qed.


Theorem the_rewrites_sound
: forall hints, RewriteHintDbOk RbaseD hints ->
    setoid_rewrite_spec RbaseD (the_rewrites hints).
Proof.
  unfold the_rewrites. intros.
  eapply rw_post_simplify_sound.
  { eapply simple_reduce_sound. }
  eapply rw_simplify_sound.
  (** This type should be named
     ** It might already be named but it should have a better name.
     ** Probably the code from RTac/Simplify.v or something that is pretty close to it
     ** And then, Red and RedAll should export functions that have this type.
     **)
  { intros.
    generalize (Red.beta_sound tus tvs e t). rewrite H0.
    intros; forward. eauto. }
  eapply using_prewrite_db_sound; eauto with typeclass_instances.
  { eapply RelDec_semidec; eauto with typeclass_instances. }
  { eapply RbaseD_single_type. }
  { eapply CompileHints_sound.
    auto. }
Qed.


Theorem monad_simplify_sound : setoid_rewrite_spec RbaseD monad_simplify.
Proof.
Admitted.
(*
  eapply repeat_rewrite_sound.
  + eapply bottom_up_sound.
    - eapply RbaseD_single_type.
    - eapply is_reflROk. eapply is_refl_ok.
    - eapply is_transROk. eapply is_trans_ok.
    - eapply the_rewrites_sound. eapply the_lemmas_sound.
    - eapply get_respectful_only_all_ex_sound.
  + eapply is_reflROk. eapply is_refl_ok.
  + eapply is_transROk. eapply is_trans_ok.
Qed.
*)

Definition rewrite_it : rtac typ (expr typ func) :=
  @auto_setoid_rewrite_bu typ func (expr typ func)
                          (Rflip (Rinj fImpl))
                          (is_reflR is_refl) (is_transR is_trans) monad_simplify get_respectful.

Theorem rewrite_it_sound : rtac_sound rewrite_it.
Proof.
  eapply auto_setoid_rewrite_bu_sound with (RbaseD := RbaseD).
  - eapply RbaseD_single_type.
  - reflexivity.
  - eapply is_reflROk; eapply is_refl_ok.
  - eapply is_transROk; eapply is_trans_ok.
  - eapply pull_all_quant_sound.
  - eapply get_respectful_sound.
Qed.

  -
Admitted.
(*
  eapply auto_setoid_rewrite_bu_sound with (RbaseD:=RbaseD).
  - eapply RbaseD_single_type.
  - reflexivity.
  - eapply is_reflROk; eapply is_refl_ok.
  - eapply is_transROk; eapply is_trans_ok.
  - eapply pull_all_quant_sound.
  - eapply get_respectful_sound.
Qed.
*)

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

  (* Examples from examples/PolyRewrite/Monad.v *)
  Check ex1.

  Goal (exists x, ex1 = x).
    unfold ex1.
    Time run_tactic reify_simple rewrite_it rewrite_it_sound.

  
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