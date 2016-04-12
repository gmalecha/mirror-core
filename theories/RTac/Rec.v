Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.CoreK.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Context {typ : Type}.
  Context {expr : Type}.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Expr_expr : Expr typ expr}.
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

  Section REC_N.
    Section rec.
      Variable b : rtac typ expr -> rtac typ expr.
      Variable last : rtac typ expr.

      Fixpoint rec_N_rec (n : BinNums.positive)
        : (rtac typ expr -> rtac typ expr) -> rtac typ expr :=
        match n with
          | BinNums.xH => fun all => all last
          | BinNums.xI n =>
            fun all e sub tus tvs =>
              rec_N_rec n (fun z e sub tus tvs => b (fun e sub tus tvs => all (fun e sub tus tvs => all z e sub tus tvs) e sub tus tvs) e sub tus tvs) e sub tus tvs
          | BinNums.xO n =>
            fun all e sub tus tvs =>
              rec_N_rec n (fun z e sub tus tvs => all (fun e sub tus tvs => all z e sub tus tvs) e sub tus tvs)
                  e sub tus tvs
        end.

      Hypothesis b_sound : forall t, rtac_sound t -> rtac_sound (b t).
      Hypothesis last_sound : rtac_sound last.

      Lemma rec_N_rec_sound
      : forall n rest, (forall t, rtac_sound t -> rtac_sound (rest t)) ->
                        rtac_sound (rec_N_rec n rest).
      Proof.
        induction n; simpl.
        { intros.
          eapply IHn. intros.
          eapply b_sound. eapply H. eapply H. assumption. }
        { intros. eapply IHn. intros.
          eapply H. eapply H. assumption. }
        { intros. eapply H. assumption. }
      Qed.

    End rec.

    Definition REC_N (n : BinNums.positive)
               (b : rtac typ expr -> rtac typ expr)
               (last : rtac typ expr)
    : rtac typ expr :=
      rec_N_rec b last n b.

    Theorem REC_N_sound
      : forall b l, (forall t, rtac_sound t -> rtac_sound (b t)) ->
                    rtac_sound l ->
                    forall n,
                      rtac_sound (REC_N n b l).
    Proof.
      intros. eapply rec_N_rec_sound; eauto.
    Qed.
  End REC_N.

  Definition RECK (n : nat)
             (b : rtacK typ expr -> rtacK typ expr)
             (last : rtacK typ expr)
  : rtacK typ expr :=
    (fix rec (n : nat) : rtacK typ expr :=
       match n with
         | 0 => b last
         | S n => fun e sub tus tvs =>
                    b (fun e sub tus tvs => rec n e sub tus tvs)
                      e sub tus tvs
       end) n.

  Theorem RECK_sound
  : forall b l, (forall t, rtacK_sound t -> rtacK_sound (b t)) ->
                rtacK_sound l ->
                forall n,
                  rtacK_sound (RECK n b l).
  Proof.
    induction n; simpl; intros; eauto.
  Qed.

End parameterized.

Arguments REC {_ _} n%nat f%rtac last%rtac _ _ _ _ _ _ _ : rename.
Arguments REC_N {_ _} n%positive_scope f%rtac last%rtac _ _ _ _ _ _ _ : rename.
Arguments RECK {_ _} n%nat f%rtacK last%rtac _ _ _ _ _ _ _ : rename.
