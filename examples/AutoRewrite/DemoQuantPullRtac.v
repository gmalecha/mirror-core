Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprD.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.RewriteRelations.
Require Import MirrorCore.Lambda.AutoSetoidRewriteRtac.
Require Import MirrorCore.Reify.Reify.
Require Import McExamples.Simple.Simple.
Require Import McExamples.Simple.SimpleReify.

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

Fixpoint goal n : expr typ func :=
  match n with
  | 0 => fEq_nat (fN 0) (fN 0)
  | S n =>
    fAnd (fEx tyNat (goal n)) (fEx tyNat (goal n))
  end.

Existing Instance RType_typ.
Existing Instance Expr.Expr_expr.

Definition RbaseD (e : expr typ func) (t : typ)
: option (TypesI.typD t -> TypesI.typD t -> Prop) :=
  exprD nil nil e (tyArr t (tyArr t tyProp)).

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
: forall T P Q, Basics.impl (Q /\ (exists n : T, P n)) (exists n, Q /\ P n).
Proof.
  destruct 1. destruct H0.
  eexists; split; eauto.
Qed.

Reify BuildLemma < reify_simple_typ reify_simple reify_concl_base >
      lem_pull_ex_nat_and_right : @pull_ex_and_right nat.

Definition lem_pull_ex_nat_and_right_sound
: Lemma.lemmaD (rw_conclD RbaseD) nil nil lem_pull_ex_nat_and_right :=
  @pull_ex_and_right nat.

Fixpoint is_refl (r : R typ (expr typ func)) : bool :=
  match r with
  | Rinj (Inj (Eq _)) => true
  | Rinj (Inj Impl) => true
  | Rpointwise _ x => is_refl x
  | Rrespects (Rinj (Inj (Eq _))) x => is_refl x
  | _ => false
  end.

Fixpoint is_trans (r : R typ (expr typ func)) : bool :=
  match r with
  | Rinj (Inj (Eq _)) => true
  | Rinj (Inj Lt) => true
  | Rinj (Inj Impl) => true
  | Rpointwise _ x => is_trans x
  | Rrespects (Rinj (Inj (Eq _))) x => is_trans x
  | _ => false
  end.

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

Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.Views.Ptrns.

Definition simple_reduce (e : expr typ func) : expr typ func :=
  run_tptrn
    (pdefault_id
       (pmap (fun abcd => let '(a,(b,(c,d),e)) := abcd in
                          App a (Abs c (App (App b d) e)))
             (app get (abs get (fun t =>
                                  app (app get (pmap (fun x => (t,Red.beta x)) get))
                                      (pmap Red.beta get))))))
    e.

Definition the_rewrites
           (lems : list (rw_lemma typ func (expr typ func) * CoreK.rtacK typ (expr typ func)))
: lem_rewriter typ func Rbase := 
  rw_post_simplify simple_reduce (rw_simplify Red.beta (using_rewrite_db rel_dec lems)).

(*
  fun e r =>
    rw_bind
      (@using_rewrite_db typ func _ _ _ _ (expr typ func) (@expr_eq_sdec typ func _ rel_dec) lems (Red.beta e) r)
      (fun e' => rw_ret (Progress (simple_reduce match e' with
                                                 | Progress e' => e'
                                                 | NoProgress => e
                                                 end))).
*)

Definition rewrite_db_sound hints : Prop :=
  Forall
    (fun
       lt : Lemma.lemma typ (expr typ func) (rw_concl typ func Rbase) *
            CoreK.rtacK typ (expr typ func) =>
     Lemma.lemmaD (rw_conclD RbaseD) nil nil (fst lt) /\
     CoreK.rtacK_sound (snd lt)) hints.

Theorem the_rewrites_sound
: forall hints, rewrite_db_sound hints ->
    setoid_rewrite_spec RbaseD (the_rewrites hints).
Proof. (*
  unfold the_rewrites. intros. 
  eapply rw_post_simplify_sound.
  { admit. }
  eapply rw_simplify_sound.
  { admit. }
  eapply using_rewrite_db_sound; eauto.
*)
Admitted.

Require Import MirrorCore.RTac.RunOnGoals.
Require Import MirrorCore.RTac.IdtacK.
Require Import MirrorCore.RTac.Minify.

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

Require Import MirrorCore.Lambda.Red.

Definition pull_all_quant : lem_rewriter typ func Rbase :=
  repeat_rewrite (fun e r =>
                    bottom_up is_refl is_trans (the_rewrites the_lemmas)
                              get_respectful_only_all_ex e r)
                 is_refl is_trans false 300.

(** this doesn't lift everything, but it does what it is programmed to do **)
Definition quant_pull (e : expr typ func) : mrw (Progressing (expr typ func)) :=
  bottom_up is_refl is_trans (pull_all_quant) get_respectful
            e (Rinj fImpl).

Fixpoint goal2 n (acc : nat) : expr typ func :=
  match n with
  | 0 =>
    if acc ?[ lt ] 8 then
      fEx tyNat (fEq_nat (fN 0) (fN 0))
    else
      fEq_nat (fN 0) (fN 0)
  | S n =>
    fAnd (goal2 n (acc * 2)) (goal2 n (acc * 2 + 1)) (*
    fAnd (fEx tyNat (goal n)) (fEx tyNat (goal n)) *)
  end.

Eval compute in goal2 1 0.

(*
Print lem_pull_ex_nat_and_left.
Goal the_rewrites (firstn 1 the_lemmas) (goal2 1 0) (Rinj fImpl) nil nil nil 0 0 (TopSubst _ nil nil) <> None.
  compute.
  simpl. unfold the_rewrites.
  unfold rw_post_simplify, rw_simplify, using_rewrite_db.
  simpl beta.
  unfold using_rewrite_db''.
  unfold for_tactic. unfold using_rewrite_db'.
  Ltac go :=
    match goal with
    | |- not (?X = _) =>
      let Y := eval red in X in change X with Y
    end.
  go. go. go. do 5 go. go. go. go.
  go.
  Ltac GO :=
    let rec find X :=
        match X with
        | match ?Y with _ => _ end => find Y
        | match ?Y with _ => _ end _ => find Y
        | match ?Y with _ => _ end _ _ => find Y
        | match ?Y with _ => _ end _ _ _ => find Y
        | match ?Y with _ => _ end _ _ _ _ => find Y
        | match ?Y with _ => _ end _ _ _ _ _ => find Y
        | match ?Y with _ => _ end _ _ _ _ _ _ => find Y
        | match ?Y with _ => _ end _ _ _ _ _ _ _ => find Y
        | match ?Y with _ => _ end _ _ _ _ _ _ _ _ => find Y
        | _ => let X' := eval compute in X in change X with X'
        end
    in
    match goal with
    | |- not (?X = _) =>
      find X
    end.
  GO.
  go.
  GO. cbv iota beta.
  GO.
  compute.


  Eval compute in (GConj_list
                   (map
                      (fun e : expr typ func =>
                       GGoal (VarsToUVars.vars_to_uvars 0 0 e))
                      (Lemma.premises lem_pull_ex_nat_and_left))).

  pose ().
  simpl in o. unfold the_rewrites in o.
  ree

Eval vm_compute
  in the_rewrites the_lemmas (goal2 1 0) (Rinj fImpl) nil nil nil 0 0 (TopSubst _ nil nil).


Eval vm_compute
  in pull_all_quant (goal2 1 0) (Rinj fImpl) nil nil nil 0 0 (TopSubst _ nil nil).


Eval vm_compute
  in quant_pull (goal2 1 0) nil nil nil 0 0 (TopSubst _ nil nil).
*)
(*
Theorem pull_ex_nat_and_left_iff
: forall T P Q, ((@ex T P) /\ Q) <-> (exists n, P n /\ Q).
Proof. Admitted.
Theorem pull_ex_nat_and_right_iff
: forall T P Q, (Q /\ (@ex T P)) <-> (exists n, Q /\ P n).
Proof. Admitted.

Goal match exprD nil nil (goal2 8 0) tyProp return Prop with
     | None => True
     | Some x => x
     end -> True.
simpl. unfold AbsAppI.exprT_App, exprT_Inj. simpl.
Require Import Morphisms.
Require Import Setoid.
Require Import RelationClasses.
intro H.
Time repeat first [ setoid_rewrite pull_ex_nat_and_left_iff in H
                  | setoid_rewrite pull_ex_nat_and_right_iff in H ].
trivial.
Time Qed.

Fixpoint repeatFunc (n : nat) (p : expr typ func -> Progressing (expr typ func))
: (expr typ func -> R typ (expr typ func) -> mrw (func:=func) (typ:=typ) (Progressing (expr typ func))) ->
  expr typ func -> R typ (expr typ func) -> mrw (func:=func) (typ:=typ) (Progressing (expr typ func)) :=
  match n with
  | 0 => fun f e r =>
           rw_bind (f e r)
                   (fun e' =>
                      match e' with
                      | NoProgress => rw_ret (p e)
                      | Progress e' => rw_ret (Progress e')
                      end)
  | S n => fun f e r =>
             rw_bind
               (f e r)
               (fun e' =>
                  match e' with
                  | NoProgress => rw_ret (p e)
                  | Progress e' => repeatFunc n (@Progress _) f e' r
                  end)
  end.
*)