(** Weakest Pre-condition for Imp **)
Require Import Coq.Strings.String.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Lambda.Expr.
Require Import McExamples.Imp.Imp.

Axiom typ : Type.

Axiom tyState : typ.
Axiom tyArr : typ -> typ -> typ.
Axiom tyProp : typ.


Inductive dfunc :=
| lfalse | ltrue | land | lor | limpl
| lforall (_ : typ) | lexists (_ : typ)
| btrue | bfalse
| leq
| lupd (s : string)
| lget (s : string).
  (** [lget] is not total b/c my environments are partial! **)

Definition func : Type := (SymEnv.func + dfunc)%type.
Definition sexpr := expr typ func.

Let df_f : dfunc -> func := @inr _ _.
Let Inj' : func -> sexpr := @Inj typ func.

Coercion Inj' : func >-> sexpr.
Coercion df_f : dfunc >-> func.

Local Notation "a @ b" := (App (a : sexpr) (b : sexpr)) (at level 30).

Axiom aexpr_to_expr : aexpr -> sexpr -> sexpr.
Axiom bexpr_to_expr : bexpr -> sexpr -> sexpr.

Fixpoint wp (e : imp) (P : sexpr) : sexpr :=
  match e with
    | Seq a b =>
      wp a (wp b P)
    | Fail => Abs tyState (lfalse : sexpr)
    | Skip => P
    | Assign v e =>
      Abs tyState (land @ (leq @ lget v @ aexpr_to_expr e (Var 0))
                        @ (P @ (lupd v @ aexpr_to_expr e (Var 0))))
    | If b t f =>
      let wpt := wp t P in
      let wpf := wp f P in
      let b' := bexpr_to_expr b (Var 0) in
      Abs tyState (lor @ (land @ (leq @ b' @ btrue) @ wpt)
                       @ (land @ (leq @ b' @ bfalse) @ wpf))
    | Loop b l =>
      (** TODO: This is not correct **)
      let wpl := wp l (Var 1) in
      let b' := bexpr_to_expr b (Var 0) in
      Abs tyState
          (lexists (tyArr tyState tyProp) @
                   (land @ (lforall tyState @
                                    (limpl @ (land @ (Var 1 @ Var 0)
                                                   @ (leq @ b' @ bfalse))
                                           @ (P @ Var 0)))
                         @ (lforall tyState @
                                    (limpl @ (land @ (leq @ b' @ btrue)
                                                   @ (wpl @ (Var 0)))
                                           @ (wpl @ (Var 0))))))
  end.

Eval compute in wp (Assign "x"%string (Const 3)) (Abs tyState (ltrue : sexpr)).