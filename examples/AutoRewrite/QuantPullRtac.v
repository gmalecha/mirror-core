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
Require Import McExamples.Simple.Simple.
Require Import McExamples.Simple.SimpleReify.

Set Implicit Arguments.
Set Strict Implicit.

(* TODO - change typ to mtyp typ' *)
(* TODO - figure out how to resolve the dependency this creates on PolyRewrite *)
(* TODO - i think MLambda will resolve this *)
Let Rbase := expr typ func.

Reify Declare Patterns patterns_concl : (rw_concl typ func Rbase).

Reify Declare Syntax reify_concl_base :=
  (CPatterns patterns_concl).

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
Reify Pattern patterns_concl += (!!(@Basics.flip Prop Prop Prop) @ !!Basics.impl @ ?0 @ ?1) =>
  (fun (a b : function reify_simple) =>
     @Build_rw_concl typ func Rbase a (Rflip (@Rinj typ Rbase (Inj Impl))) b).

Existing Instance RType_typ.
Existing Instance Expr.Expr_expr.

Definition RbaseD (e : expr typ func) (t : typ)
: option (TypesI.typD t -> TypesI.typD t -> Prop) :=
  env_exprD nil nil (tyArr t (tyArr t tyProp)) e.

(** TODO: Try to get rid of this **)
(*
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
*)

Theorem pull_ex_and_left
: forall T P Q, Basics.flip Basics.impl ((@ex T P) /\ Q) (exists n, P n /\ Q).
Proof.
  do 2 red. intros.
  destruct H. destruct H. split; eauto.
Qed.

Reify BuildLemma < reify_simple_typ reify_simple reify_concl_base >
      lem_pull_ex_nat_and_left : @pull_ex_and_left nat.

Definition lem_pull_ex_nat_and_left_sound
: Lemma.lemmaD (rw_conclD RbaseD) nil nil lem_pull_ex_nat_and_left :=
  @pull_ex_and_left nat.

Theorem pull_ex_and_right
: forall T P Q, Basics.flip Basics.impl (Q /\ (@ex T P)) (exists n, Q /\ P n).
Proof.
  destruct 1. destruct H.
  split; eauto.
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
    unfold env_exprD. simpl. intros.
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
    unfold env_exprD. simpl. intros.
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
    unfold env_exprD. simpl. intros.
    autorewrite with exprD_rw in H0.
    forward. inv_all; subst.
    unfold symAs in H0. unfold typeof_sym in H0.
    unfold RSym_func in H0.
    unfold typeof_func in H0.
    forward. }
  { unfold RbaseD; simpl.
    unfold env_exprD. simpl. intros.
    autorewrite with exprD_rw in H0.
    forward. inv_all; subst.
    unfold symAs in H0. unfold typeof_sym in H0.
    unfold RSym_func in H0.
    unfold typeof_func in H0.
    forward. inv_all. subst.
    simpl. clear. inversion r.
    subst. rewrite (UIP_refl r). compute. congruence. }
  { unfold RbaseD; simpl.
    unfold env_exprD. simpl. intros.
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

Definition flip_impl : R typ Rbase := Rflip (Rinj (Inj Impl)).


Require Import MirrorCore.Lambda.Rewrite.Respectful.
Local Open Scope Rrespects_scope.
  Definition get_respectful_only_all_ex : ResolveProper typ func Rbase :=
    do_respectful rel_dec
                  ((Pr' ((tyNat ***> flip_impl) ===> flip_impl) (Inj (Ex tyNat))) ::
                                                                                  (Pr' (Rrespects (Rpointwise tyNat flip_impl) flip_impl) (Inj (All tyNat))) :: nil).

  Definition get_respectful : ResolveProper typ func Rbase :=
    do_respectful rel_dec
                  ((Pr' (Rrespects (Rpointwise tyNat flip_impl) flip_impl) (Inj (Ex tyNat))) ::
                                                                                             (Pr' (Rrespects (Rpointwise tyNat flip_impl) flip_impl) (Inj (All tyNat))) ::
                                                                                             (Pr' (Rrespects flip_impl (Rrespects flip_impl flip_impl)) (Inj And)) ::
                                                                                             (Pr' (Rrespects flip_impl (Rrespects flip_impl flip_impl)) (Inj Or)) ::
                                                                                             (Pr' (Rrespects (Rinj (Inj (Eq tyNat))) (Rrespects (Rinj (Inj (Eq tyNat))) (Rinj (Inj (Eq tyNat))))) (Inj Plus)) ::
                                                                                             nil).

  Local Close Scope Rrespects_scope.


Theorem get_respectful_only_all_ex_sound
: respectful_spec RbaseD get_respectful_only_all_ex.
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

(* TODO: The rest of this file is broken, and essentially is subsumed by
   PolyQuantpullRtac anyway. We should figure out whether to remove it. *)
(*
Require Import MirrorCore.Lambda.Rtac.
Require Import MirrorCore.Types.ModularTypes.

Definition the_rewrites (lems : RewriteHintDb Rbase (*list (rw_lemma typ func (expr typ func) *
                                      CoreK.rtacK typ (expr typ func)) *))
: RwAction typ func Rbase :=
  rw_post_simplify simple_reduce (rw_simplify Red.beta (using_prewrite_db rel_dec (CompileHints lems))).


Theorem the_rewrites_sound
: forall hints, rewrite_db_sound RbaseD hints ->
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


(** This should be a HintDb *)
Definition the_lemmas
: list (rw_lemma typ func (expr typ func) * CoreK.rtacK typ (expr typ func)) :=
  (lem_pull_ex_nat_and_left, IDTACK) ::
  (lem_pull_ex_nat_and_right, IDTACK) ::
  nil.

Theorem the_lemmas_sound : rewrite_db_sound RbaseD the_lemmas.
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
*)