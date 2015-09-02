Require Import MirrorCore.ExprI.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprUnify.
Require Import MirrorCore.Lambda.Lemma.
Require Import MirrorCore.RTac.RTac.
Require Import McExamples.Cancel.Lang.

Set Implicit Arguments.
Set Strict Implicit.

Section canceller.
  Variables typ func : Type.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Typ0_Prop : Typ0 RType_typ Prop}.
  Context {Typ2_func : Typ2 RType_typ RFun}.
  Context {Typ2Ok_func : Typ2Ok Typ2_func}.
  Context {RSym_sym : RSym func}.
  Context {RSymOk_sym : RSymOk RSym_sym}.

  Let Expr_expr := @Expr_expr typ func RType_typ _ _.
  Local Existing Instance Expr_expr.
  Let ExprOk_expr : ExprOk Expr_expr := @ExprOk_expr typ func _ _ _ _ _ _.
  Local Existing Instance ExprOk_expr.
  Local Existing Instance ExprUVarOk_expr.

  Variable T : typ.
  Variable R P U : expr typ func.

  Let p (a b : expr typ func) : expr typ func :=
    App (App P a) b.
  Let r (a b : expr typ func) : expr typ func :=
    App (App R a) b.

  Definition lem_plus_unit_c : Lemma.lemma typ (expr typ func) (expr typ func) :=
  {| vars := T :: T :: nil;
     premises := App (App R (ExprCore.Var 0)) (ExprCore.Var 1) :: nil;
     concl := App (App R (ExprCore.Var 0))  (App (App P U) (ExprCore.Var 1)) |}.
  Definition lem_plus_assoc_c1 : Lemma.lemma typ (expr typ func) (expr typ func) :=
  {| vars := T :: T :: T :: T :: nil;
     premises := App (App R (ExprCore.Var 3))
                     (App (App P (ExprCore.Var 0))
                          (App (App P (ExprCore.Var 1)) (ExprCore.Var 2))) :: nil;
     concl := App (App R (ExprCore.Var 3))
                  (App (App P (App (App P (ExprCore.Var 0)) (ExprCore.Var 1)))
                       (ExprCore.Var 2)) |}.
  Definition lem_plus_assoc_c2 : Lemma.lemma typ (expr typ func) (expr typ func) :=
  {| vars := T :: T :: T :: T :: nil;
     premises := App (App R (ExprCore.Var 3))
                     (App (App P (ExprCore.Var 1))
                          (App (App P (ExprCore.Var 0)) (ExprCore.Var 2))) :: nil;
     concl := App (App R (ExprCore.Var 3))
                  (App (App P (App (App P (ExprCore.Var 0)) (ExprCore.Var 1)))
                       (ExprCore.Var 2)) |}.
  Definition lem_plus_comm_c : Lemma.lemma typ (expr typ func) (expr typ func) :=
  {| vars := T :: T :: T :: nil;
     premises := App (App R (ExprCore.Var 2))
                     (App (App P (ExprCore.Var 0)) (ExprCore.Var 1)) :: nil;
     concl := App (App R (ExprCore.Var 2))
                  (App (App P (ExprCore.Var 1)) (ExprCore.Var 0)) |}.
  Definition lem_plus_cancel : Lemma.lemma typ (expr typ func) (expr typ func) :=
  {| vars := T :: T :: T :: T :: nil;
     premises := App (App R (ExprCore.Var 0)) (ExprCore.Var 2)
                     :: App (App R (ExprCore.Var 1)) (ExprCore.Var 3)
                     :: nil;
     concl := App
                (App R (App (App P (ExprCore.Var 0)) (ExprCore.Var 1)))
                (App (App P (ExprCore.Var 2)) (ExprCore.Var 3)) |}.

  Definition lem_plus_unit_p : Lemma.lemma typ (expr typ func) (expr typ func) :=
  {| vars := T :: T :: nil;
     premises := App (App R (ExprCore.Var 0)) (ExprCore.Var 1) :: nil;
     concl := App (App R (App (App P U) (ExprCore.Var 0)))
                  (ExprCore.Var 1) |}.
  Definition lem_plus_assoc_p1 : Lemma.lemma typ (expr typ func) (expr typ func) :=
  {| vars := T :: T :: T :: T :: nil;
     premises := App
                   (App R
                        (App (App P (ExprCore.Var 0))
                             (App (App P (ExprCore.Var 1)) (ExprCore.Var 2))))
                   (ExprCore.Var 3) :: nil;
     concl := App
                (App R
                     (App (App P (App (App P (ExprCore.Var 0)) (ExprCore.Var 1)))
                          (ExprCore.Var 2))) (ExprCore.Var 3) |}.
  Definition lem_plus_assoc_p2 : Lemma.lemma typ (expr typ func) (expr typ func) :=
  {| vars := T :: T :: T :: T :: nil;
     premises := App
                   (App R
                        (App (App P (ExprCore.Var 1))
                             (App (App P (ExprCore.Var 0)) (ExprCore.Var 2))))
                   (ExprCore.Var 3) :: nil;
     concl := App
                (App R
                     (App (App P (App (App P (ExprCore.Var 0)) (ExprCore.Var 1)))
                          (ExprCore.Var 2))) (ExprCore.Var 3) |}.
  Definition lem_plus_comm_p : Lemma.lemma typ (expr typ func) (expr typ func) :=
  {| vars := T :: T :: T :: nil;
     premises := App
                   (App R
                        (App (App P (ExprCore.Var 0)) (ExprCore.Var 1)))
                   (ExprCore.Var 2) :: nil;
     concl := App
                (App R (App (App P (ExprCore.Var 1)) (ExprCore.Var 0)))
                (ExprCore.Var 2) |}.
  Context {RL1 : ReifiedLemma lem_plus_unit_c}.
  Context {RL2 : ReifiedLemma lem_plus_assoc_c1}.
  Context {RL3 : ReifiedLemma lem_plus_assoc_c2}.
  Context {RL4 : ReifiedLemma lem_plus_comm_c}.
  Context {RL5 : ReifiedLemma lem_plus_cancel}.
  Context {RL6 : ReifiedLemma lem_plus_unit_p}.
  Context {RL7 : ReifiedLemma lem_plus_assoc_p1}.
  Context {RL8 : ReifiedLemma lem_plus_assoc_p2}.
  Context {RL9 : ReifiedLemma lem_plus_comm_p}.

  Definition EAPPLY (l : Lemma.lemma typ (expr typ func) (expr typ func)) : rtac typ (expr typ func) :=
    THEN (@EAPPLY _ _ _ _ _ _ (fun subst Ssubst SUsubst => @exprUnify subst _ _ _ _ _ Ssubst SUsubst 30) l) (@MINIFY _ _ _ _ _).
  Definition APPLY (l : Lemma.lemma typ (expr typ func) (expr typ func)) : rtac typ (expr typ func) :=
    THEN (@APPLY _ _ _ _ _ _ (fun subst Ssubst SUsubst => @exprUnify subst _ _ _ _ _ Ssubst SUsubst 30) l) (@MINIFY _ _ _ _ _).
  Definition ON_EACH : list (rtac typ (expr typ func)) -> rtacK typ (expr typ func) :=
    ON_EACH.
  Definition ON_ALL : rtac typ (expr typ func) -> rtacK typ (expr typ func) := ON_ALL.

  Local Instance RtacSound_EAPPLY l (RL : ReifiedLemma l)
  : RtacSound _ _ (EAPPLY l).
  Proof.
    constructor.
    eapply THEN_sound.
    eapply EAPPLY_sound; eauto with typeclass_instances.
    intros. eapply exprUnify_sound; eauto with typeclass_instances.
    eapply MINIFY_sound; eauto with typeclass_instances.
  Qed.

  Local Instance RtacSound_APPLY l (RL : ReifiedLemma l)
  : RtacSound _ _ (APPLY l).
  Proof.
    constructor.
    eapply THEN_sound.
    eapply APPLY_sound; eauto with typeclass_instances.
    intros. eapply exprUnify_sound; eauto with typeclass_instances.
    eapply MINIFY_sound; eauto with typeclass_instances.
  Qed.

  Lemma ON_EACH_sound
  : forall ls, Forall rtac_sound ls -> rtacK_sound (ON_EACH ls).
  Proof. eapply ON_EACH_sound. Qed.
  Lemma ON_ALL_sound : forall t, rtac_sound t -> rtacK_sound (ON_ALL t).
  Proof. eapply ON_ALL_sound. Qed.

  Variable SOLVER : rtac typ (expr typ func).
  Variable RtacSound_SOLVER : RtacSound _ _ SOLVER.

  Definition iter_right (n : nat) : rtac typ (expr typ func) :=
    REC n (fun rec =>
    FIRST (   EAPPLY lem_plus_unit_c
           :: THEN (EAPPLY lem_plus_assoc_c1) (ON_ALL rec)
           :: THEN (EAPPLY lem_plus_assoc_c2) (ON_ALL rec)
           :: THEN (EAPPLY lem_plus_cancel)
                   (ON_EACH (SOLVE SOLVER :: IDTAC :: nil))
           :: nil))
        IDTAC.

  Opaque FIRST APPLY EAPPLY.

  Existing Class rtac_sound.
  Existing Instance RtacSound_proof.

  Lemma iter_right_sound : forall Q, rtac_sound (iter_right Q).
  Proof.
    unfold iter_right. intros.
    rtac_derive_soundness_default.
    eapply ON_EACH_sound; rtac_derive_soundness_default.
  Qed.

  Section afterwards.
    Variable k : rtac typ (expr typ func).
    Definition iter_left (n : nat) : rtac typ (expr typ func) :=
      REC n (fun rec =>
      FIRST (   EAPPLY lem_plus_unit_p
             :: THEN (EAPPLY lem_plus_assoc_p1) (ON_ALL rec)
             :: THEN (EAPPLY lem_plus_assoc_p2) (ON_ALL rec)
             :: k
             :: nil))
          IDTAC.

    Hypothesis k_sound : rtac_sound k.

    Lemma iter_left_sound : forall Q, rtac_sound (iter_left Q).
    Proof.
      unfold iter_left. intros.
      rtac_derive_soundness_default.
    Qed.
  End afterwards.

  Definition cancel' (n m : nat) : rtac typ (expr typ func) :=
    let k :=
        FIRST (   THEN (EAPPLY lem_plus_comm_c) (ON_ALL (iter_right m))
               :: iter_right m
               :: nil)
    in
    FIRST (   iter_left k n
           :: THEN (EAPPLY lem_plus_comm_p) (ON_ALL (iter_left k n))
           :: nil).

  Lemma cancel'_sound : forall P Q, rtac_sound (cancel' P Q).
  Proof.
    cbv beta delta [ cancel' ].
    intros.
    match goal with
      | |- rtac_sound (let x := ?X in _) =>
        assert (rtac_sound X); [ | generalize dependent X ]
    end; simpl; intros;
    rtac_derive_soundness_default; eauto using iter_right_sound, iter_left_sound.
  Qed.

  Fixpoint size (e : expr typ func) : nat :=
    match e with
      | App (App _ x) y => size x + size y
      | _ => 1
    end.

  Definition cancel : rtac typ (expr typ func) :=
    AT_GOAL (fun _ _ e =>
               let fuel := size e in
               REPEAT fuel
                      (FIRST (   SOLVE SOLVER
                              :: THEN (THEN (cancel' fuel fuel) (ON_ALL (TRY SOLVER)))
                                      (@MINIFY _ _ _ _ _)
                              :: nil))).

  Theorem cancel_sound : rtac_sound cancel.
  Proof.
    unfold cancel.
    rtac_derive_soundness_default; eauto using cancel'_sound with typeclass_instances.
  Qed.

End canceller.

(*
Fixpoint build_plusL n : expr typ func :=
  match n with
    | 0 => Inj (N 1)
    | S n' => App (App (Inj Plus) (Inj (N (S n)))) (build_plusL n')
  end.

Fixpoint build_plusR n : expr typ func :=
  match n with
    | 0 => Inj (N 1)
    | S n' => App (App (Inj Plus) (build_plusR n')) (Inj (N (S n)))
  end.

Definition goal n := App (App (Inj (Eq tyNat)) (build_plusL n)) (build_plusR n).

Time Eval vm_compute in @runRtac _ _ nil nil (goal 200) automation.

Eval vm_compute in goal 1.
Goal True.

vm_compute in r.
*)

(**
Definition lem_plus_unit_c : Lemma.lemma typ (expr typ func) (expr typ func) :=
{|
vars := T :: T :: nil;
premises := App (App (Inj (Eq T)) (ExprCore.Var 1)) (ExprCore.Var 0) :: nil;
concl := App (App R (ExprCore.Var 1))  (App (App P U) (ExprCore.Var 0)) |}.
reify_simple_lemma plus_unit_c.
Show Proof. Defined.
Definition lem_plus_assoc_c1 : Lemma.lemma typ (expr typ func) (expr typ func).
reify_simple_lemma plus_assoc_c1.
Defined.
Definition lem_plus_assoc_c2 : Lemma.lemma typ (expr typ func) (expr typ func).
reify_simple_lemma plus_assoc_c2.
Defined.
Definition lem_plus_comm_c : Lemma.lemma typ (expr typ func) (expr typ func).
reify_simple_lemma plus_comm_c.
Defined.
Definition lem_plus_cancel : Lemma.lemma typ (expr typ func) (expr typ func).
reify_simple_lemma plus_cancel.
Defined.

Definition lem_plus_unit_p : Lemma.lemma typ (expr typ func) (expr typ func).
reify_simple_lemma plus_unit_p.

Defined.
Definition lem_plus_assoc_p1 : Lemma.lemma typ (expr typ func) (expr typ func).
reify_simple_lemma plus_assoc_p1.
Defined.
Definition lem_plus_assoc_p2 : Lemma.lemma typ (expr typ func) (expr typ func).
reify_simple_lemma plus_assoc_p2.
Defined.
Definition lem_plus_comm_p : Lemma.lemma typ (expr typ func) (expr typ func).
reify_simple_lemma plus_comm_p.
Defined.
Definition lem_refl : Lemma.lemma typ (expr typ func) (expr typ func).
reify_simple_lemma refl.
Defined.
**)