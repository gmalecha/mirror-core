Require Import McExamples.Cancel.Monoid.

Module Demo (M : Monoid).
  Import M.

  Local Infix "&" := P (at level 50).
  Local Infix "%is" := R (at level 70).

  Ltac ltac_canceler :=
    let cancel P Q :=
        let rec iter_right Q :=
            match Q with
            | ?L & ?R =>
              (apply plus_assoc_c1 ; iter_right L)
              || (apply plus_assoc_c2 ; iter_right R)
            | _ =>
              apply plus_cancel; [ apply refl | ]
            end
        in
        let rec iter_left P :=
            match P with
            | ?L & ?R =>
              (apply plus_assoc_p1 ; iter_left L)
              || (apply plus_assoc_p2 ; iter_left R)
            | _ =>
              match Q with
              | ?A & ?B =>
                iter_right A
                || (apply plus_comm_c; iter_right B)
              end
            end
        in
        match P with
        | ?A & ?B =>
          iter_left A
          || (apply plus_comm_p; iter_left B)
        end
    in
    repeat match goal with
           | [ |- ?P %is ?Q ] =>
             apply refl || cancel P Q
           end.

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

    Theorem test1 : goal 10.
      prep.
      Time ltac_canceler.
    Time Qed.
    Print Assumptions test1.
  End Demo.
End Demo.
