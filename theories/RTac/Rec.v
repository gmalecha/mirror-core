Require Import MirrorCore.RTac.Core.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Definition REC (n : nat)
             (b : rtac typ expr subst -> rtac typ expr subst)
             (last : rtac typ expr subst)
  : rtac typ expr subst :=
    (fix rec (n : nat) : rtac typ expr subst :=
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
  Context {Subst_subst : Subst subst expr}.
  Context {SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst}.

  Variables tus tvs : tenv typ.

  Theorem REC_sound
  : forall b l, (forall t, rtac_sound tus tvs t -> rtac_sound tus tvs (b t)) ->
                rtac_sound tus tvs l ->
                forall n,
                  rtac_sound tus tvs (REC n b l).
  Proof.
    induction n; simpl; intros; eauto.
  Qed.

End parameterized.

Arguments REC {_ _ _} n f last _ _ _ _ _ _ _ : rename.