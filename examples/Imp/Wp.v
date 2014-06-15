(** Weakest Pre-condition for Imp **)
Require Import Coq.Strings.String.
Require Import MirrorCore.Lambda.Expr.
Require Import McExamples.Imp.Imp.

Local Notation "a @ b" := (App a b) (at level 30).

Axiom typ : Type.
Axiom func : Type.

Definition sexpr := expr typ func.

Axiom tyState : typ.
Axiom tyArr : typ -> typ -> typ.
Axiom tyProp : typ.

Axiom lfalse : sexpr.
Axiom land : sexpr -> sexpr -> sexpr.
Axiom lor : sexpr -> sexpr -> sexpr.
Axiom limpl : sexpr -> sexpr -> sexpr.
Axiom lexists : typ -> sexpr -> sexpr.
Axiom lforall : typ -> sexpr -> sexpr.
Axiom btrue : sexpr.
Axiom bfalse : sexpr.
Axiom lupd : string -> sexpr -> sexpr.
Axiom leq : sexpr -> sexpr -> sexpr.
Axiom lget : string -> sexpr.

Axiom aexpr_to_expr : aexpr -> sexpr -> sexpr.
Axiom bexpr_to_expr : bexpr -> sexpr -> sexpr.


Fixpoint wp (e : imp) (P : sexpr) : sexpr :=
  match e with
    | Seq a b =>
      wp a (wp b P)
    | Fail => (Abs tyState lfalse)
    | Skip => P
    | Write v e =>
      Abs tyState (land (leq (lget v) (aexpr_to_expr e (Var 0)))
                        (App P (lupd v (aexpr_to_expr e (Var 0)))))
    | If b t f =>
      let wpt := wp t P in
      let wpf := wp f P in
      let b' := bexpr_to_expr b (Var 0) in
      Abs tyState (lor (land (leq b' btrue) wpt)
                       (land (leq b' bfalse) wpf))
    | Loop b l =>
      let wpl := wp l (Var 1) in
      let b' := bexpr_to_expr b (Var 0) in
      Abs tyState (lexists (tyArr tyState tyProp)
                           (land (lforall tyState
                                          (limpl (land (App (Var 1) (Var 0))
                                                       (leq b' bfalse))
                                                 (App P (Var 0))))
                                 (lforall tyState
                                          (limpl (land (leq b' btrue)
                                                       (wpl @ (Var 0)))
                                                 (wpl @ (Var 0))))))
      
  end.