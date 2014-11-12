Require Import MirrorCore.RTac.Core.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Context {typ : Type}.
  Context {expr : Type}.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.
  Context {ExprUVar_expr : ExprUVar expr}.
  Context {ExprUVarOk_expr : ExprUVarOk _}.

  Definition REC (n : nat)
             (b : rtac typ expr -> rtac typ expr)
             (last : rtac typ expr)
  : rtac typ expr :=
    (fix rec (n : nat) : rtac typ expr :=
       match n with
         | 0 => b last
         | S n => fun e sub tus tvs =>
                    b (fun e sub tus tvs => rec n e sub tus tvs)
                      e sub tus tvs
       end) n.

  Theorem REC_sound
  : forall b l, (forall t, rtac_sound t -> rtac_sound (b t)) ->
                rtac_sound l ->
                forall n,
                  rtac_sound (REC n b l).
  Proof.
    induction n; simpl; intros; eauto.
  Qed.

End parameterized.

Arguments REC {_ _} n f last _ _ _ _ _ _ _ : rename.