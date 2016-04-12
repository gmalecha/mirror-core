Require Import MirrorCore.ExprI.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprUnify.
Require Import MirrorCore.Lambda.Lemma.
Require Import MirrorCore.RTac.RTac.
Require Import McExamples.Cancel.MonoidLemmasSyntax.

Set Implicit Arguments.
Set Strict Implicit.

(* This code purposefully does not use the reification mechanism so that it
 * can remain agnostic to the underlying implementation.
 *)
Section canceller.
  Variables typ func : Type.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Typ0_Prop : Typ0 RType_typ Prop}.
  Context {Typ2_func : Typ2 RType_typ RFun}.
  Context {Typ2Ok_func : Typ2Ok Typ2_func}.
  Context {RSym_sym : RSym func}.
  Context {RSymOk_sym : RSymOk RSym_sym}.
  Let Expr_expr : Expr typ (expr typ func) := Expr_expr.
  Local Existing Instance Expr_expr.
  Let ExprOk_expr : ExprOk Expr_expr := ExprOk_expr.
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

  Definition EAPPLY : Lemma.lemma typ (expr typ func) (expr typ func) -> rtac typ (expr typ func) :=
    EAPPLY (fun subst Ssubst SUsubst => exprUnify 30).
  Definition APPLY : Lemma.lemma typ (expr typ func) (expr typ func) -> rtac typ (expr typ func) :=
    APPLY (fun subst Ssubst SUsubst => exprUnify 30).

  Local Instance RtacSound_EAPPLY l (RL : ReifiedLemma l)
  : RtacSound (EAPPLY l).
  Proof.
    constructor.
    eapply EAPPLY_sound; eauto with typeclass_instances.
    intros. eapply exprUnify_sound; eauto with typeclass_instances.
  Qed.

  Local Instance RtacSound_APPLY l (RL : ReifiedLemma l)
  : RtacSound (APPLY l).
  Proof.
    constructor.
    eapply APPLY_sound; eauto with typeclass_instances.
    intros. eapply exprUnify_sound; eauto with typeclass_instances.
  Qed.

  Variable SOLVER : rtac typ (expr typ func).
  Variable RtacSound_SOLVER : RtacSound SOLVER.

  Notation "'delay' x" := (fun y => x y) (at level 3).

  Fixpoint iter_right (Q : expr typ func) : rtac typ (expr typ func) :=
    FIRST [ EAPPLY lem_plus_unit_c
          | delay match Q with
                  | App (App _ L) R => (* guess star *)
                    FIRST [ EAPPLY lem_plus_assoc_c1 ;; delay (ON_ALL (iter_right L))
                          | EAPPLY lem_plus_assoc_c2 ;; delay (ON_ALL (iter_right R))
                          | EAPPLY lem_plus_cancel ;; ON_EACH (SOLVE SOLVER :: IDTAC :: nil)
                          ]
                   | _ =>
                     EAPPLY lem_plus_cancel ;; ON_EACH [ SOLVE SOLVER | IDTAC ]
                 end ].

  Opaque FIRST APPLY EAPPLY.

  Existing Class rtac_sound.
  Existing Instance RtacSound_proof.

  Lemma body_non_c
  : rtac_sound
     (FIRST [ EAPPLY lem_plus_unit_c
            | delay (EAPPLY lem_plus_cancel ;;
                     ON_EACH [ SOLVE SOLVER | IDTAC ]) ]).
  Proof.
    intros. rtac_derive_soundness_default.
  Qed.

  Lemma iter_right_sound : forall Q, rtac_sound (iter_right Q).
  Proof.
    eapply expr_strong_ind; eauto using body_non_c.
    intros.
    simpl. destruct a; eauto using body_non_c.
    rtac_derive_soundness_default.
    - eapply H. eapply TransitiveClosure.LTStep; eauto.
      eapply acc_App_r.
      eapply TransitiveClosure.LTFin; eauto.
      eapply acc_App_l.
    - eapply H.
      eapply TransitiveClosure.LTFin; eauto.
      eapply acc_App_r.
  Qed.

  Section afterwards.
    Variable k : rtac typ (expr typ func).
    Fixpoint iter_left (P : expr typ func) : rtac typ (expr typ func) :=
      FIRST [ EAPPLY lem_plus_unit_p
            | delay match P with
                    | App (App _ L) R => (* guess star *)
                      FIRST [ EAPPLY lem_plus_assoc_p1 ;; delay (ON_ALL (iter_left L))
                            | EAPPLY lem_plus_assoc_p2 ;; delay (ON_ALL (iter_left R))
                            | k
                            ]
                     | _ => k
                   end ].
    Hypothesis k_sound : rtac_sound k.
    Lemma body_non_p : rtac_sound (FIRST [ EAPPLY lem_plus_unit_p | delay k ]).
    Proof. rtac_derive_soundness_default. Qed.

    Lemma iter_left_sound : forall Q, rtac_sound (iter_left Q).
    Proof.
      eapply expr_strong_ind; eauto using body_non_p.
      simpl. destruct a; eauto using body_non_p.
      intros.
      rtac_derive_soundness_default; eapply H.
      - eapply TransitiveClosure.LTStep; eauto.
        eapply acc_App_r.
        eapply TransitiveClosure.LTFin; eauto.
        eapply acc_App_l.
      - eapply TransitiveClosure.LTFin; eauto.
        eapply acc_App_r.
    Qed.
  End afterwards.

  Definition cancel' (P Q : expr typ func) : rtac typ (expr typ func) :=
    let k :=
        match Q with
          | App (App _ A) B =>
            FIRST [ EAPPLY lem_plus_comm_c ;; delay (ON_ALL (iter_right B))
                  | iter_right A
                  ]
          | _ => FAIL
        end
    in
    match P with
      | App (App _ A) B =>
        FIRST [ iter_left k A
              | (* TODO(gmalecha): What is the purpose of this line? *)
                FAIL ;; ON_ALL (THEN (EAPPLY lem_plus_comm_p) (delay (ON_ALL (iter_left k B))))
              ]
      | _ => FAIL
    end.

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
               REPEAT (size e)
                      (FIRST [ SOLVER
                             | AT_GOAL (fun _ _ e =>
                                          match e with
                                          | App (App _ L) R =>
                                            FIRST [ cancel' L R ;;
                                                    ON_ALL (TRY SOLVER) ]
                                          | _ => FAIL
                                          end) ;; MINIFY
                             ])).

  Theorem cancel_sound : rtac_sound cancel.
  Proof.
    unfold cancel.
    rtac_derive_soundness_default; eauto using cancel'_sound with typeclass_instances.
  Qed.

End canceller.