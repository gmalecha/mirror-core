(* This is a demo of developing a cancellation algorithm for
 * commutative monoids.
 *)
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require MirrorCore.syms.SymEnv.
Require MirrorCore.syms.SymSum.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.Rtac.
Require Import MirrorCore.Reify.Reify.

Require Import McExamples.Cancel.Monoid.
Require McExamples.Cancel.MonoidSyntaxModular.

Set Implicit Arguments.
Set Strict Implicit.

Module MonoidCancel (M : Monoid).

  Local Infix "&" := M.P (at level 50).
  Local Infix "%is" := M.R (at level 70).

  (* Import the syntactic language *)
  Module Syntax := MonoidSyntaxModular.Syntax M.
  Import Syntax.

  (* A little bit of verification magic *)
  Hint Extern 0 (ReifiedLemma _) =>
  (constructor;
  solve [ exact M.plus_unit_c
        | exact M.plus_assoc_c1
        | exact M.plus_assoc_c2
        | exact M.plus_comm_c
        | exact M.plus_cancel
        | exact M.plus_unit_p
        | exact M.plus_assoc_p1
        | exact M.plus_assoc_p2
        | exact M.plus_comm_p
        | exact M.refl ]) : typeclass_instances.

  (* Write the automation *)
  Section with_solver.
    Variable fs : SymEnv.functions typ.
    Let RSym_func := RSym_func fs.
    Local Existing Instance RSym_func.
    Let Expr_expr : Expr typ (expr typ func) := Expr.Expr_expr.
    Local Existing Instance Expr_expr.

    Let ExprOk_expr : ExprOk Expr_expr := ExprOk_expr.
    Local Existing Instance ExprOk_expr.

    (** The Automation, parameterized by a sound solver.
     **)
    Variable solver : rtac typ (expr typ func).
    Hypothesis solver_ok : RtacSound solver.

    Definition iter_right (n : nat) : rtac typ (expr typ func) :=
      REC n (fun rec =>
               FIRST [ EAPPLY <:: M.plus_unit_c ::>
                     | EAPPLY <:: M.plus_assoc_c1 ::> ;; ON_ALL rec
                     | EAPPLY <:: M.plus_assoc_c2 ::> ;; ON_ALL rec
                     | EAPPLY <:: M.plus_cancel ::> ;;
                              ON_EACH [ SOLVE solver | IDTAC ]
                     ])
          IDTAC.

    Instance iter_right_sound {Q} : RtacSound (iter_right Q).
    Proof. unfold iter_right; rtac_derive_soundness_default. Qed.

    Section afterwards.
      Variable k : rtac typ (expr typ func).
      Definition iter_left (n : nat) : rtac typ (expr typ func) :=
        REC n (fun rec =>
                 FIRST [ EAPPLY <:: M.plus_unit_p ::>
                       | EAPPLY <:: M.plus_assoc_p1 ::> ;; ON_ALL rec
                       | EAPPLY <:: M.plus_assoc_p2 ::> ;; ON_ALL rec
                       | k
                       ])
            IDTAC.

      Hypothesis k_sound : RtacSound k.



      Lemma iter_left_sound : forall Q, RtacSound (iter_left Q).
      Proof. unfold iter_left; rtac_derive_soundness_default. Qed.
    End afterwards.
    Local Existing Instance iter_left_sound.

    Definition cancel' (n m : nat) : rtac typ (expr typ func) :=
      let k :=
          FIRST [ EAPPLY <:: M.plus_comm_c ::> ;; ON_ALL (iter_right m)
                | iter_right m
                ]
      in
      FIRST [ iter_left k n
            | EAPPLY <:: M.plus_comm_p ::> ;; ON_ALL (iter_left k n)
            ].

    Local Instance cancel'_sound : forall P Q, RtacSound (cancel' P Q).
    Proof. cbv beta delta [ cancel' ]; rtac_derive_soundness_default. Qed.

    Fixpoint size (e : expr typ func) : nat :=
      match e with
      | App (App _ x) y => size x + size y
      | _ => 1
      end.

    Definition cancel : rtac typ (expr typ func) :=
      AT_GOAL (fun _ _ e =>
                 let fuel := size e in
                 REPEAT fuel
                        (FIRST [ SOLVE solver
                               | (cancel' fuel fuel ;; ON_ALL (TRY solver)) ;;
                                 MINIFY
                               ])).

    Theorem cancel_sound : RtacSound cancel.
    Proof.
      unfold cancel.
      rtac_derive_soundness_default; eauto with typeclass_instances.
    Qed.

  End with_solver.

  Definition the_tactic fs :=
    @cancel fs (EAPPLY (RSym_sym:=RSym_func fs) <:: M.refl ::>).

  Theorem the_tactic_sound fs
  : rtac_sound (Expr_expr:=the_Expr fs) (the_tactic fs).
  Proof.
    unfold the_tactic.
    intros. eapply cancel_sound; eauto with typeclass_instances.
  Qed.

  (** The example *)
  Module Demo.
    Axiom N : nat -> M.M.

    Fixpoint build_plusL n : M.M :=
      match n with
      | 0 => N 0
      | S n' => M.P (N n) (build_plusL n')
      end.

    Fixpoint build_plusR n : M.M :=
      match n with
      | 0 => N 0
      | S n' => M.P (build_plusR n') (N n)
      end.

    Definition goal n := M.R (build_plusL n) (build_plusR n).

    Ltac prep := unfold goal, build_plusL, build_plusR.

    Ltac rtac_canceler :=
      run_tbl_rtac the_Expr the_tactic the_tactic_sound.

    Theorem test1 : goal 100.
      prep.
      Time rtac_canceler.
    Time Qed.
    Print Assumptions test1.
  End Demo.

End MonoidCancel.
