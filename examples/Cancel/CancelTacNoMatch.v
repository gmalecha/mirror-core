Require Import MirrorCore.ExprI.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprUnify.
Require Import MirrorCore.Lambda.Lemma.
Require Import MirrorCore.RTac.RTac.
Require Import McExamples.Cancel.MonoidLemmasSyntax.

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
About Expr_expr.
  Let Expr_expr := @Expr_expr typ func RType_typ _ _.
  Local Existing Instance Expr_expr.
  Let ExprOk_expr : ExprOk Expr_expr := @ExprOk_expr typ func _ _ _ _ _ _.
  Local Existing Instance ExprOk_expr.
  Local Existing Instance ExprUVarOk_expr.

  Variable T : typ.
  Variable R P U : expr typ func.

  Let lem_plus_unit_c := lem_plus_unit_c T R P U.
  Let lem_plus_assoc_c1 := lem_plus_assoc_c1 T R P.
  Let lem_plus_assoc_c2 := lem_plus_assoc_c2 T R P.
  Let lem_plus_comm_c := lem_plus_comm_c T R P.
  Let lem_plus_cancel := lem_plus_cancel T R P.
  Let lem_plus_unit_p := lem_plus_unit_p T R P U.
  Let lem_plus_assoc_p1 := lem_plus_assoc_p1 T R P.
  Let lem_plus_assoc_p2 := lem_plus_assoc_p2 T R P.
  Let lem_plus_comm_p := lem_plus_comm_p T R P.

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
    (EAPPLY (fun subst Ssubst SUsubst => exprUnify 30) l ;; MINIFY)%rtac.
  Definition APPLY (l : Lemma.lemma typ (expr typ func) (expr typ func)) : rtac typ (expr typ func) :=
    (APPLY (fun subst Ssubst SUsubst => exprUnify 30) l ;; MINIFY)%rtac.

  Local Instance RtacSound_EAPPLY l (RL : ReifiedLemma l)
  : RtacSound (EAPPLY l).
  Proof.
    constructor.
    eapply THEN_sound.
    eapply EAPPLY_sound; eauto with typeclass_instances.
    intros. eapply exprUnify_sound; eauto with typeclass_instances.
    eapply MINIFY_sound; eauto with typeclass_instances.
  Qed.

  Local Instance RtacSound_APPLY l (RL : ReifiedLemma l)
  : RtacSound (APPLY l).
  Proof.
    constructor.
    eapply THEN_sound.
    eapply APPLY_sound; eauto with typeclass_instances.
    intros. eapply exprUnify_sound; eauto with typeclass_instances.
    eapply MINIFY_sound; eauto with typeclass_instances.
  Qed.

  Variable SOLVER : rtac typ (expr typ func).
  Variable RtacSound_SOLVER : RtacSound SOLVER.

  Definition iter_right (n : nat) : rtac typ (expr typ func) :=
    REC n (fun rec =>
             FIRST [ EAPPLY lem_plus_unit_c
                   | EAPPLY lem_plus_assoc_c1 ;; ON_ALL rec
                   | EAPPLY lem_plus_assoc_c2 ;; ON_ALL rec
                   | EAPPLY lem_plus_cancel ;;
                     ON_EACH [ SOLVE SOLVER | IDTAC ]
                   ])
        IDTAC.

  Opaque FIRST APPLY EAPPLY.

  Existing Class rtac_sound.
  Existing Instance RtacSound_proof.

  Lemma iter_right_sound : forall Q, rtac_sound (iter_right Q).
  Proof.
    unfold iter_right. intros.
    rtac_derive_soundness_default.
  Qed.

  Section afterwards.
    Variable k : rtac typ (expr typ func).
    Definition iter_left (n : nat) : rtac typ (expr typ func) :=
      REC n (fun rec =>
               FIRST [ EAPPLY lem_plus_unit_p
                     | EAPPLY lem_plus_assoc_p1 ;; ON_ALL rec
                     | EAPPLY lem_plus_assoc_p2 ;; ON_ALL rec
                     | k
                     ])
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
        FIRST [ EAPPLY lem_plus_comm_c ;; ON_ALL (iter_right m)
              | iter_right m
              ]
    in
    FIRST [ iter_left k n
          | EAPPLY lem_plus_comm_p ;; ON_ALL (iter_left k n)
          ].

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
                      (FIRST [ SOLVE SOLVER
                             | (cancel' fuel fuel ;; ON_ALL (TRY SOLVER)) ;; MINIFY
                             ])).

  Theorem cancel_sound : rtac_sound cancel.
  Proof.
    unfold cancel.
    rtac_derive_soundness_default; eauto using cancel'_sound with typeclass_instances.
  Qed.

End canceller.
