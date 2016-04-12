Require Import MirrorCore.Lemma.
Require Import MirrorCore.Lambda.Expr.

Set Implicit Arguments.
Set Strict Implicit.

(* This code purposefully does not use the reification mechanism so that it
 * can remain agnostic to the underlying implementation.
 *)
Section cancel_lemmas.
  Context {typ func : Type}.
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
End cancel_lemmas.
