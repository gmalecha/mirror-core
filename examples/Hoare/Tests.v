(** This file contains some example programs that I can verify
 **)
Require Import Coq.Strings.String.
Require Import McExamples.Hoare.Imp.

Module TestCases (Import Imp : ImpLang).

  Local Notation "x ;; y" := (Seq x y) (at level 30, y at next level).
  Local Notation "x <- y" := (Assign x%string y) (at level 20).
  Local Notation "$ x" := (iVar x%string) (at level 5).
  Let iConst' : nat -> iexpr := iConst.
  Local Coercion iConst' : nat >-> iexpr.

  Local Open Scope string_scope.

  Definition Add1 : icmd :=
    "x"    <- (iPlus $"x" 1).

  Definition Swap : icmd :=
    "temp" <- $"x" ;;
           "x"    <- $"y" ;;
           "y"    <- $"temp".

  Fixpoint Swap_n (ls : list (string * string)) : icmd :=
    match ls with
    | nil => Skip
    | cons (x,y) ls =>
      Seq (Assign "temp" (iVar x))
          (Seq (Assign x (iVar y))
               (Seq (Assign y (iVar "temp"))
                    (Swap_n ls)))
    end.

(*
  Fixpoint Swap_ptr_n (ls : list (string * string)) : icmd :=
    match ls with
    | nil => Skip
    | cons (x,y) ls =>
      Seq (Read "temp1" (iVar x))
          (Seq (Read "temp2" (iVar y))
               (Seq (Assign x (iVar "temp2"))
                    (Seq (Assign y (iVar "temp1"))
                         (Swap_ptr_n ls))))
    end.
*)

  Definition IfZero : icmd :=
    If $"x"
       ("y" <- 1)
       ("y" <- 0).

  (*
Definition While : icmd :=
  While (iLt $"x" 10)
        ("x" <- iPlus $"x" 1).
   *)

  Fixpoint adds (n : nat) :=
    match n with
    | 0 => Skip
    | 1 => (Assign "x" (iPlus (iVar "x") (iConst 1)))
    | S n => Seq (Assign "x" (iPlus (iVar "x") (iConst 1))) (adds n)
    end%string.

  Fixpoint skips (n : nat) :=
    match n with
    | 0 => Skip
    | S n => Seq Skip (skips n)
    end%string.
End TestCases.