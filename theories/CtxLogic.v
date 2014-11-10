Require Import MirrorCore.ExprI.
Require Import ExtLib.Data.HList.

Section parameterized.
  Context {typ expr : Type}.
  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr RType_typ expr}.

  (** NOTE: This interface is less modular than is desireable
   ** It should really be generalized to arbitrary logics on the right.
   ** - Note the isomorphism between [exprT nil nil Prop] and [Prop] to
   **   derive this interface from that one
   **)
  Class ExprTApplicative {tus tvs} (C : exprT tus tvs Prop -> Prop) : Type :=
  { exprTPure : forall (P : exprT _ _ Prop), (forall us vs, P us vs) -> C P
  ; exprTAp   : forall (P Q : exprT _ _ Prop),
                  C (fun us vs => P us vs -> Q us vs) ->
                  C P -> C Q }.

  Global Instance ExprTApplicative_foralls tus tvs
  : ExprTApplicative
      (fun P : exprT tus tvs Prop =>
         forall (us : hlist typD tus) (vs : hlist typD tvs), P us vs).
  Proof.
    clear. constructor; firstorder.
  Defined.

  Global Instance ExprTApplicative_foralls_impl tus tvs P'
  : ExprTApplicative
      (fun P : exprT tus tvs Prop =>
         forall (us : hlist typD tus) (vs : hlist typD tvs),
           P' us vs -> P us vs).
  Proof.
    clear. constructor; firstorder.
  Defined.

End parameterized.