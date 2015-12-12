Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.Compat.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprD.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.RewriteRelations.
Require Import MirrorCore.Lambda.AutoSetoidRewriteRtac.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.RTac.IdtacK.
Require Import McExamples.Simple.Simple.
Require Import McExamples.Simple.SimpleReify.

Set Implicit Arguments.
Set Strict Implicit.

Let Rbase := expr typ func.

Reify Declare Patterns patterns_concl := (rw_concl typ func Rbase).

Reify Declare Syntax reify_concl_base :=
  (@CPatterns _ patterns_concl).

Local Notation "x @ y" := (@RApp x y) (only parsing, at level 30).
Local Notation "'!!' x" := (@RExact _ x) (only parsing, at level 25).
Local Notation "'?' n" := (@RGet n RIgnore) (only parsing, at level 25).
Local Notation "'?!' n" := (@RGet n RConst) (only parsing, at level 25).
Local Notation "'#'" := RIgnore (only parsing, at level 0).

Reify Pattern patterns_concl += (?0 @ ?1 @ ?2) =>
  (fun (a b c : function reify_simple) =>
     @Build_rw_concl typ func Rbase b (@Rinj typ Rbase a) c).
Reify Pattern patterns_concl += (!!Basics.impl @ ?0 @ ?1) =>
  (fun (a b : function reify_simple) =>
     @Build_rw_concl typ func Rbase a (@Rinj typ Rbase (Inj Impl)) b).

Existing Instance RType_typ.
Existing Instance Expr.Expr_expr.

Definition RbaseD (e : expr typ func) (t : typ)
: option (TypesI.typD t -> TypesI.typD t -> Prop) :=
  exprD nil nil e (tyArr t (tyArr t tyProp)).

Theorem RbaseD_single_type
: forall (r : expr typ func) (t1 t2 : typ)
         (rD1 : TypesI.typD t1 -> TypesI.typD t1 -> Prop)
         (rD2 : TypesI.typD t2 -> TypesI.typD t2 -> Prop),
    RbaseD r t1 = Some rD1 -> RbaseD r t2 = Some rD2 -> t1 = t2.
Proof.
  unfold RbaseD, exprD. simpl; intros.
  forward.
  generalize (exprD'_deterministic _ _ _ H0 H). unfold Rty.
  intros. inversion H3. reflexivity.
Qed.

Theorem pull_ex_and_left
: forall T P Q, Basics.impl ((@ex T P) /\ Q) (exists n, P n /\ Q).
Proof.
  red. intros.
  destruct H. destruct H. eexists; split; eauto.
Qed.

Reify BuildLemma < reify_simple_typ reify_simple reify_concl_base >
      lem_pull_ex_nat_and_left : @pull_ex_and_left nat.

Definition lem_pull_ex_nat_and_left_sound
: Lemma.lemmaD (rw_conclD RbaseD) nil nil lem_pull_ex_nat_and_left :=
  @pull_ex_and_left nat.

Theorem pull_ex_and_right
: forall T P Q, Basics.impl (Q /\ (@ex T P)) (exists n, Q /\ P n).
Proof.
  destruct 1. destruct H0.
  eexists; split; eauto.
Qed.

Reify BuildLemma < reify_simple_typ reify_simple reify_concl_base >
      lem_pull_ex_nat_and_right : @pull_ex_and_right nat.

Definition lem_pull_ex_nat_and_right_sound
: Lemma.lemmaD (rw_conclD RbaseD) nil nil lem_pull_ex_nat_and_right :=
  @pull_ex_and_right nat.

Definition is_refl : refl_dec Rbase :=
  fun (r : Rbase) =>
    match r with
    | Inj (Eq _)
    | Inj Impl => true
    | _ => false
    end.

(* TODO(gmalecha): The majority the complexity of this file comes from
 * simplifying the denotation function. A few tactics should improve this
 * dramatically.
 *)
Theorem is_refl_ok : refl_dec_ok RbaseD is_refl.
Proof.
  red.
  destruct r; simpl; try congruence.
  destruct f; simpl; try congruence.
  { unfold RbaseD; simpl.
    unfold exprD. simpl. intros.
    autorewrite with exprD_rw in H0.
    forward. inv_all; subst.
    unfold symAs in H0. unfold typeof_sym in H0.
    unfold RSym_func in H0.
    unfold typeof_func in H0.
    forward. inv_all. subst. simpl.
    clear. red in r. inversion r.
    subst.
    rewrite (UIP_refl r). compute. reflexivity. }
  { unfold RbaseD; simpl.
    unfold exprD. simpl. intros.
    autorewrite with exprD_rw in H0.
    forward. inv_all; subst.
    unfold symAs in H0. unfold typeof_sym in H0.
    unfold RSym_func in H0.
    unfold typeof_func in H0.
    forward. inv_all. subst. simpl.
    clear. red in r. inversion r.
    subst.
    rewrite (UIP_refl r). compute. intros; tauto. }
Qed.

Definition is_trans : trans_dec Rbase :=
  fun r =>
    match r with
    | Inj (Eq _)
    | Inj Lt
    | Inj Impl => true
    | _ => false
    end.

Theorem is_trans_ok : trans_dec_ok RbaseD is_trans.
Proof.
  red.
  destruct r; simpl; try congruence.
  destruct f; simpl; try congruence.
  { unfold RbaseD; simpl.
    unfold exprD. simpl. intros.
    autorewrite with exprD_rw in H0.
    forward. inv_all; subst.
    unfold symAs in H0. unfold typeof_sym in H0.
    unfold RSym_func in H0.
    unfold typeof_func in H0.
    forward. }
  { unfold RbaseD; simpl.
    unfold exprD. simpl. intros.
    autorewrite with exprD_rw in H0.
    forward. inv_all; subst.
    unfold symAs in H0. unfold typeof_sym in H0.
    unfold RSym_func in H0.
    unfold typeof_func in H0.
    forward. inv_all. subst.
    simpl. clear. inversion r.
    subst. rewrite (UIP_refl r). compute. congruence. }
  { unfold RbaseD; simpl.
    unfold exprD. simpl. intros.
    autorewrite with exprD_rw in H0.
    forward. inv_all; subst.
    unfold symAs in H0. unfold typeof_sym in H0.
    unfold RSym_func in H0.
    unfold typeof_func in H0.
    forward. inv_all. subst.
    clear. inversion r. subst.
    rewrite (UIP_refl r).
    compute. tauto. }
Qed.

Definition get_respectful_only_all_ex : respectful_dec typ func Rbase :=
  do_respectful rel_dec
    ((Inj (Ex tyNat), Rrespects (Rpointwise tyNat (Rinj (Inj Impl))) (Rinj (Inj Impl))) ::
     (Inj (All tyNat), Rrespects (Rpointwise tyNat (Rinj (Inj Impl))) (Rinj (Inj Impl))) ::
     nil).

Definition get_respectful : respectful_dec typ func Rbase :=
  do_respectful rel_dec
    ((Inj (Ex tyNat), Rrespects (Rpointwise tyNat (Rinj (Inj Impl))) (Rinj (Inj Impl))) ::
     (Inj (All tyNat), Rrespects (Rpointwise tyNat (Rinj (Inj Impl))) (Rinj (Inj Impl))) ::
     (Inj And, Rrespects (Rinj (Inj Impl)) (Rrespects (Rinj (Inj Impl)) (Rinj (Inj Impl)))) ::
     (Inj Or, Rrespects (Rinj (Inj Impl)) (Rrespects (Rinj (Inj Impl)) (Rinj (Inj Impl)))) ::
     (Inj Plus, Rrespects (Rinj (Inj (Eq tyNat))) (Rrespects (Rinj (Inj (Eq tyNat))) (Rinj (Inj (Eq tyNat))))) ::

nil).


Lemma RelDec_semidec {T} (rT : T -> T -> Prop) (RDT : RelDec rT) (RDOT : RelDec_Correct RDT)
: forall a b : T, a ?[ rT ] b = true -> rT a b.
Proof. intros. consider (a ?[ rT ] b); auto. Qed.

Theorem get_respectful_only_all_ex_sound : respectful_spec RbaseD get_respectful_only_all_ex.
Proof.
  eapply do_respectful_sound.
  - eapply RelDec_semidec; eauto with typeclass_instances.
  - repeat first [ eapply Forall_cons | eapply Forall_nil ]; simpl.
    { compute. firstorder. }
    { compute. firstorder. }
Qed.

Theorem get_respectful_sound : respectful_spec RbaseD get_respectful.
Proof.
  eapply do_respectful_sound.
  - eapply RelDec_semidec; eauto with typeclass_instances.
  - repeat first [ eapply Forall_cons | eapply Forall_nil ]; simpl.
    { compute. firstorder. }
    { compute. firstorder. }
    { compute. firstorder. }
    { compute. firstorder. }
    { compute. firstorder. }
Qed.

Definition simple_reduce (e : expr typ func) : expr typ func :=
  run_ptrn_id
    (pmap (fun abcd => let '(a,(b,(c,d),e)) := abcd in
                       App a (Abs c (App (App b d) e)))
          (app get (abs get (fun t =>
                               app (app get
                                        (pmap (fun x => (t,Red.beta x)) get))
                                   (pmap Red.beta get)))))
    e.

Definition the_rewrites
           (lems : list (rw_lemma typ func (expr typ func) * CoreK.rtacK typ (expr typ func)))
: lem_rewriter typ func Rbase :=
  rw_post_simplify simple_reduce (rw_simplify Red.beta (using_rewrite_db rel_dec lems)).

(** TODO(gmalecha): Move **)
Definition rewrite_db_sound hints : Prop :=
  Forall
    (fun
       lt : Lemma.lemma typ (expr typ func) (rw_concl typ func Rbase) *
            CoreK.rtacK typ (expr typ func) =>
     Lemma.lemmaD (rw_conclD RbaseD) nil nil (fst lt) /\
     CoreK.rtacK_sound (snd lt)) hints.

Lemma simple_reduce_sound :
  forall (tus tvs : tenv typ) (t : typ) (e : expr typ func)
         (eD : exprT tus tvs (TypesI.typD t)),
    ExprDsimul.ExprDenote.exprD' tus tvs t e = Some eD ->
    exists eD' : exprT tus tvs (TypesI.typD t),
      ExprDsimul.ExprDenote.exprD' tus tvs t (simple_reduce e) = Some eD' /\
      (forall (us : HList.hlist TypesI.typD tus)
              (vs : HList.hlist TypesI.typD tvs), eD us vs = eD' us vs).
Proof.
  unfold simple_reduce.
  intros.
  eapply run_ptrn_id_sound; eauto with typeclass_instances.
  { repeat first [ simple eapply ptrn_ok_pmap
                 | simple eapply ptrn_ok_app
                 | simple eapply ptrn_ok_abs; intros
                 | simple eapply ptrn_ok_get
                 ]. }
  { intros. ptrnE.
    eapply exprD'_Abs_prem in H0; forward_reason; subst.
    inv_all. subst.
    generalize (Red.beta_sound tus (x4 :: tvs) x10 x6).
    generalize (Red.beta_sound tus (x4 :: tvs) x7 x).
    simpl. Cases.rewrite_all_goal. intros; forward.
    erewrite exprD'_App; try eassumption.
    2: erewrite exprD'_Abs; try eauto with typeclass_instances.
    2: rewrite typ2_match_iota; eauto with typeclass_instances.
    2: rewrite type_cast_refl; eauto with typeclass_instances.
    2: erewrite exprD'_App; try eassumption.
    3: erewrite exprD'_App; try eassumption; eauto.
    2: autorewrite_with_eq_rw; reflexivity.
    simpl. eexists; split; eauto.
    unfold AbsAppI.exprT_App, AbsAppI.exprT_Abs. simpl.
    intros. unfold Rrefl, Rcast_val, Rcast, Relim; simpl.
    f_equal. apply FunctionalExtensionality.functional_extensionality.
    intros. rewrite H5. rewrite H6. reflexivity. }
Qed.

Theorem the_rewrites_sound
: forall hints, rewrite_db_sound hints ->
    setoid_rewrite_spec RbaseD (the_rewrites hints).
Proof.
  unfold the_rewrites. intros.
  eapply rw_post_simplify_sound.
  { eapply simple_reduce_sound. }
  eapply rw_simplify_sound.
  { intros.
    generalize (Red.beta_sound tus tvs e t). rewrite H0.
    intros; forward. eauto. }
  eapply using_rewrite_db_sound; eauto.
  { eapply RelDec_semidec; eauto with typeclass_instances. }
  { eapply RbaseD_single_type. }
Qed.

Definition the_lemmas : list (rw_lemma typ func (expr typ func) * CoreK.rtacK typ (expr typ func)) :=
  (lem_pull_ex_nat_and_left, IDTACK) ::
  (lem_pull_ex_nat_and_right, IDTACK) ::
  nil.

Theorem the_lemmas_sound : rewrite_db_sound the_lemmas.
Proof.
  repeat first [ apply Forall_cons; [ simple apply conj | ] | apply Forall_nil ];
  simpl; solve [ apply IDTACK_sound
               | exact (@pull_ex_and_right nat)
               | exact (@pull_ex_and_left nat) ].
Qed.

Definition pull_all_quant : lem_rewriter typ func Rbase :=
  repeat_rewrite (fun e r =>
                    bottom_up (is_reflR is_refl) (is_transR is_trans) (the_rewrites the_lemmas)
                              get_respectful_only_all_ex e r)
                 (is_reflR is_refl) (is_transR is_trans) false 300.

Theorem pull_all_quant_sound : setoid_rewrite_spec RbaseD pull_all_quant.
Proof.
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

Definition quant_pull : lem_rewriter _ _ _ :=
  bottom_up (is_reflR is_refl) (is_transR is_trans) pull_all_quant get_respectful.

Theorem quant_pull_sound : setoid_rewrite_spec RbaseD quant_pull.
Proof.
  eapply bottom_up_sound.
  - eapply RbaseD_single_type.
  - eapply is_reflROk. eapply is_refl_ok.
  - eapply is_transROk. eapply is_trans_ok.
  - eapply pull_all_quant_sound.
  - eapply get_respectful_sound.
Qed.


(** Begin Demo **)
(****************)
Definition fAnd a b : expr typ func := App (App (Inj Simple.And) a) b.
Definition fOr a b : expr typ func := App (App (Inj Simple.And) a) b.
Definition fAll t P : expr typ func := App (Inj (Simple.All t)) (Abs t P).
Definition fEx t P : expr typ func := App (Inj (Simple.Ex t)) (Abs t P).
Definition fEq t : expr typ func := (Inj (Simple.Eq t)).
Definition fImpl : expr typ func := (Inj Simple.Impl).
Definition fEq_nat a b : expr typ func := App (App (fEq tyNat) a) b.
Definition fN n : expr typ func := Inj (Simple.N n).


Definition run_quant_pull e :=
  quant_pull e (Rinj fImpl).

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

Fixpoint count_quant (e : expr typ func) : nat :=
  match e with
  | App (Inj (Ex _)) (Abs _ e') => S (count_quant e')
  | _ => 0
  end.

(*
Eval compute in goal2 5 0.

Eval vm_compute
  in pull_all_quant (goal2 1 0) (Rinj fImpl) nil nil nil 0 0 (TopSubst _ nil nil).

Time Eval vm_compute
  in quant_pull (goal2 2 0) (Rinj fImpl) nil nil nil 0 0 (TopSubst _ nil nil).
*)

Definition benchmark (n m : nat) : unit :=
  match quant_pull (goal2 m n 0) (Rinj fImpl) nil nil nil 0 0 (TopSubst _ nil nil)
  with
  | Some _ => tt
  | _ => tt
  end.

(*
Eval vm_compute
  in match run_quant_pull (goal2 7 0) nil nil nil 0 0 (TopSubst _ nil nil) with
     | Some (Progress e, _) => count_quant e
     | _ => 0
     end.
*)