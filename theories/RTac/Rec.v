Require Import MirrorCore.RTac.Core.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.

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

  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.

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