Require Import McExamples.Hoare.ILogic.
Require Import McExamples.Hoare.Imp.

Module ImpTheory (Import I : ImpLang).
  Axiom entails_exL
  : forall (P : value -> locals -> HProp) Q,
    (forall x, P x |-- Q) ->
    lexists P |-- Q.

  Axiom go_lower
    : forall (P Q : lprop) (G : SProp),
      G |-- lforall (fun x : locals => embed (P x |-- Q x)) ->
      G |-- @embed Prop SProp EmbedOp_Prop_SProp (P |-- Q).

  Axiom go_lower_raw
    : forall (P Q : lprop),
      (forall x : locals, P x |-- Q x) ->
      (P |-- Q).

  Axiom embed_ltrue
    : forall (P : Prop),
      P ->
      |-- @embed Prop SProp _ P.

  Axiom locals_get_locals_upd
    : forall v val m,
      locals_get v (locals_upd v val m) = val.

  Axiom eval_iexpr_iPlus
    : forall a b m,
      eval_iexpr (iPlus a b) m = eval_iexpr a m + eval_iexpr b m.

  Axiom eval_iexpr_iVar
    : forall a m,
      eval_iexpr (iVar a) m = locals_get a m.

  Axiom eval_iexpr_iConst
    : forall a m,
      eval_iexpr (iConst a) m = a.

  Axiom pull_embed_hyp
    : forall (P : Prop) (Q R : HProp),
      (P -> (Q |-- R)) ->
      Q //\\ embed P |-- R.
  Axiom pull_embed_last_hyp
    : forall (P : Prop) (R : HProp),
      (P -> |-- R) ->
      embed P |-- R.


  Theorem Assign_seq_rule
    : forall G P Q x e c,
      G |-- triple (Exists v' : value, (fun l =>
                                          P  (locals_upd x v' l) //\\
                                             embed (locals_get x l = eval_iexpr e (locals_upd x v' l)))) c Q ->
      G |-- triple P
        (Seq (Assign x e) c)
        Q.
  Proof.
    intros. eapply Seq_rule. eapply Assign_rule. eassumption.
  Qed.

  Theorem Assign_tail_rule
    : forall G P Q x e,
      G |-- embed (Exists v' : value, (fun l => 
                                         P  (locals_upd x v' l) //\\
                                            embed (locals_get x l = eval_iexpr e (locals_upd x v' l))) |-- Q) ->
      G |-- triple P (Assign x e) Q.
  Proof.
    intros.
    eapply Conseq_rule. 3: eapply Assign_rule.
    2: eapply H.
    etransitivity. eapply ltrueR. eapply embed_ltrue. reflexivity.
  Qed.

  Theorem Skip_seq_rule
    : forall G P Q c,
      G |-- triple P c Q ->
      G |-- triple P (Seq Skip c) Q.
  Proof.
    intros. eapply Seq_rule. eapply Skip_rule_refl. eassumption.
  Qed.

  Definition Skip_tail_rule := Skip_rule.

  Theorem Assert_seq_rule
    : forall G P Q A c,
      G |-- embed (P |-- A) ->
      G |-- triple A c Q ->
      G |-- triple P (Seq (Assert A) c) Q.
  Proof.
    intros. eapply Seq_rule; [ | eapply H0 ].
    eapply Conseq_rule; [ eassumption | | eapply Assert_rule ].
    etransitivity. eapply ltrueR. eapply embed_ltrue. reflexivity.
  Qed.

  Theorem Assert_tail_rule
    : forall G P Q A,
      G |-- embed (P |-- A) ->
      G |-- embed (A |-- Q) ->
      G |-- triple P (Assert A) Q.
  Proof.
    intros. eapply Conseq_rule; try eassumption.
    eapply Assert_rule.
  Qed.

  (** Charge Lemmas **)
  Axiom and_split
    : forall G P Q : I.HProp,
      @ILogic.lentails I.HProp I.ILogicOps_HProp
                       G P ->
      @ILogic.lentails I.HProp I.ILogicOps_HProp
                       G Q ->
      @ILogic.lentails I.HProp I.ILogicOps_HProp
                       G
                       (@ILogic.land I.HProp I.ILogicOps_HProp P Q).
  Axiom prove_Prop :
    forall P : Prop,
      P ->
      @ILogic.lentails I.HProp I.ILogicOps_HProp
                       (@ILogic.ltrue I.HProp I.ILogicOps_HProp)
                       (@ILogic.embed Prop I.HProp I.EmbedOp_Prop_HProp P).

  Axiom land_apply
    : forall P Q x,
      @ILogic.land I.lprop I.ILogicOps_lprop P Q x =
      @ILogic.land I.HProp I.ILogicOps_HProp (P x) (Q x).
  Axiom get_upd_not
    : forall x y x0 m,
      x <> y ->
      I.locals_get x (I.locals_upd y x0 m) =
      I.locals_get x m.


(** Read and Write rules requiring separation logic
  Theorem Read_seq_rule
    : forall G (P Q : lprop) x e (v : locals -> value) c,
      (G |-- embed (P |-- ap (T := Fun locals) (ap (pure PtsTo) (eval_iexpr e)) v ** ltrue)) ->
      (G |-- triple (Exists v' : value, fun l =>
                                          P (locals_upd x v' l)
                                            //\\  embed (locals_get x l = v (locals_upd x v' l))) c Q) ->
      G |-- triple P (Seq (Read x e) c) Q.
  Proof.
    intros. eapply Seq_rule. eapply Read_rule. eapply H. assumption.
  Qed.

  Theorem Read_tail_rule
    : forall G (P Q : lprop) x e (v : locals -> value),
      (G |-- embed (P |-- ap (T := Fun locals) (ap (pure PtsTo) (eval_iexpr e)) v ** ltrue)) ->
      (G |-- embed (Exists v' : value, (fun l =>
                                          P (locals_upd x v' l)
                                            //\\  embed (locals_get x l = v (locals_upd x v' l))) |-- Q)) ->
      G |-- triple P (Read x e) Q.
  Proof.
    intros. eapply Conseq_rule; [ | | eapply Read_rule ].
    3: eassumption. eassumption.
  Qed.

  Theorem Write_seq_rule
    : forall G (P Q R : lprop) p v c,
      (G |-- embed (P |-- Exists v', ap (T := Fun locals) (ap (pure PtsTo) (eval_iexpr p)) (pure v') ** Q)) ->
      (G |-- triple (ap (T := Fun locals) (ap (pure PtsTo) (eval_iexpr p)) (eval_iexpr v) ** Q) c R) ->
      G |-- triple P (Seq (Write p v) c) R.
  Proof.
    intros. eapply Seq_rule. eapply Write_rule. eassumption. eassumption.
  Qed.

  Theorem Write_tail_rule
    : forall G (P Q R : lprop) p v,
      G |-- embed (P |-- Exists v', ap (T := Fun locals) (ap (pure PtsTo) (eval_iexpr p)) (pure v') ** Q) ->
      (G |-- embed ((ap (T := Fun locals) (ap (pure PtsTo) (eval_iexpr p)) (eval_iexpr v) ** Q) |-- R)) ->
      G |-- triple P (Write p v) R.
  Proof.
    intros. eapply Conseq_rule. 3: eapply Write_rule. 2: eassumption. 2: eassumption.
  Qed.
*)


End ImpTheory.