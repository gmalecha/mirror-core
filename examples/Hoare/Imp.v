Require Import Coq.Strings.String.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.Fun.
Require Import McExamples.Hoare.ILogic.

Set Implicit Arguments.
Set Strict Implicit.

Local Instance Applicative_Fun A : Applicative (Fun A) :=
{ pure := fun _ x _ => x
; ap := fun _ _ f x y => (f y) (x y)
}.

Module Type ImpLang.

  Definition var := string.
  Definition value := nat.

  (* States *)
  Parameter locals : Type.
  Parameter locals_upd : var -> value -> locals -> locals.
  Parameter locals_get : var -> locals -> value.

  (* Expressions *)
  Parameter iexpr : Type.
  Parameter iConst : value -> iexpr.
  Parameter iVar : var -> iexpr.
  Parameter iPlus : iexpr -> iexpr -> iexpr.
  Parameter iEq : iexpr -> iexpr -> iexpr.
  Parameter iLt : iexpr -> iexpr -> iexpr.

  Parameter eval_iexpr : iexpr -> locals -> value.

  (* Commands *)
  Parameter icmd : Type.

  Parameter Skip : icmd.
  Parameter Seq : icmd -> icmd -> icmd.
  Parameter Assign : var -> iexpr -> icmd.
  Parameter If : iexpr -> icmd -> icmd -> icmd.

  (* Logic for the Axiomatic Semantics *)
  Universe Uall Ulogic.
  Parameter HProp : Type@{Ulogic}. (* Predicates over the global state *)

  Parameter ILogicOps_HProp : ILogicOps@{Uall Ulogic} HProp.
  Parameter ILogic_HProp : ILogic HProp.
  Parameter EmbedOp_Prop_HProp : EmbedOp Prop HProp.
  Parameter Embed_Prop_HProp : Embed Prop HProp.

  Parameter SProp : Type@{Ulogic}. (* The specification logic *)

  Parameter ILogicOps_SProp : ILogicOps@{Uall Ulogic} SProp.
  Parameter ILogic_SProp : ILogic SProp.
  Parameter EmbedOp_Prop_SProp : EmbedOp Prop SProp.
  Parameter Embed_Prop_SProp : Embed Prop SProp.

  Definition lprop := locals -> HProp.

  Instance ILogicOps_lprop : ILogicOps@{Uall Ulogic} lprop := _.
  Instance ILogic_lprop : ILogic lprop := _.

  Instance EmbedOp_HProp_lprop : EmbedOp@{Ulogic Ulogic} HProp lprop := _.
  Instance Embed_HProp_lprop : Embed HProp lprop := _.

  (* Axiomatics Semantics *)
  Parameter triple : lprop -> icmd -> lprop -> SProp.

  (** Consequence **)
  Axiom Conseq_rule
  : forall G P P' Q' Q c,
      G |-- embed (P |-- P') ->
      G |-- embed (Q' |-- Q) ->
      G |-- triple P' c Q' ->
      G |-- triple P c Q.

  (** Quantifier Rules **)
  Axiom triple_exL
  : forall G P c Q,
      (G |-- Forall x : value, triple (P x) c Q) ->
      G |-- triple (lexists P) c Q.

  Axiom triple_pureL
  : forall (P : Prop) G c Q R,
      (G //\\ embed P |-- triple Q c R) ->
      G |-- triple (land (embed (embed P)) Q) c R.

  Lemma entails_exL
    : forall (P : value -> locals -> HProp) Q,
      (forall x, P x |-- Q) ->
      lexists P |-- Q.
  Proof.
    intros. apply lexistsL. eassumption.
  Qed.

  Lemma go_lower
    : forall (P Q : lprop) (G : SProp),
      G |-- lforall (fun x : locals => embed (P x |-- Q x)) ->
      G |-- @embed Prop SProp EmbedOp_Prop_SProp (P |-- Q).
  Proof.
    intros.
    etransitivity; [ eassumption | clear ].
    unfold embed. simpl.
    etransitivity; [ eapply embedlforall | ].
    simpl. reflexivity.
  Qed.
  Lemma go_lower_raw
    : forall (P Q : lprop),
      (forall x : locals, P x |-- Q x) ->
      (P |-- Q).
  Proof.
    red; simpl; intros.
    eapply H.
  Qed.

  (** Skip **)
  Axiom Skip_rule_refl
  : forall G P,
      G |-- triple P Skip P.

  Theorem Skip_rule
  : forall G P Q,
      G |-- embed (P |-- Q) ->
      G |-- triple P Skip Q.
  Proof.
    intros.
    eapply Conseq_rule; [ | | eapply Skip_rule_refl ].
    - eassumption.
    - eapply embed_drop.
      admit.
  Admitted.

  (** Sequence **)
  Axiom Seq_rule
  : forall G P Q R c1 c2,
      G |-- triple P c1 Q ->
      G |-- triple Q c2 R ->
      G |-- triple P (Seq c1 c2) R.

  Axiom SeqA_rule
  : forall G P Q c1 c2 c3,
      G |-- triple P (Seq c1 (Seq c2 c3)) Q ->
      G |-- triple P (Seq (Seq c1 c2) c3) Q.

  (** Assignment **)
  Axiom Assign_rule
  : forall G P x e,
    G |-- triple P
                 (Assign x e)
                 (fun l => Exists v' : value,
                             P  (locals_upd x v' l) //\\
                             embed (locals_get x l = eval_iexpr e (locals_upd x v' l))).

  (** Assert **)
  Parameter Assert : lprop -> icmd.

  Axiom Assert_rule
  : forall G (Q : lprop),
      G |-- triple Q (Assert Q) Q.

  (** If **)
  Axiom If_rule
  : forall (G : SProp) (P Q : lprop) (x : iexpr) (c1 c2 : icmd),
      G |-- triple (P //\\ (fun l : locals => embed (eval_iexpr x l <> 0))) c1 Q ->
      G |-- triple (P //\\ (fun l : locals => embed (eval_iexpr x l = 0))) c2  Q ->
      G |-- triple P (If x c1 c2) Q.


  Definition update {T} (f : locals -> locals) (m : locals -> T) (l : locals)
  : T := m (f l).

End ImpLang.

(*
Definition local_Prop_lprop (P : Fun locals Prop) : lprop :=
  fun l => embed (P l).

Definition exprProp (P : value -> Prop) (e : locals -> value) : lprop :=
  local_Prop_lprop (fun l => P (e l)).

(*
Eval cbv beta iota zeta delta [ exprProp local_Prop_lprop ] in
  forall G (P Q : lprop) x c1 c2,
    G |-- triple (P //\\ exprProp (fun v => v <> 0) (eval_iexpr x)) c1 Q ->
    G |-- triple (P //\\ exprProp (fun v => v = 0) (eval_iexpr x)) c2 Q ->
    G |-- triple P (If x c1 c2) Q.
*)



(** Read **)
Parameter Read : var -> iexpr -> icmd.

Parameter PtsTo : value -> value -> HProp.

Axiom Read_rule
: forall G (P : lprop) x e (v : locals -> value),
    (G |-- embed (P |-- ap (T := Fun locals) (ap (pure PtsTo) (eval_iexpr e)) v ** ltrue)) ->
    G |-- triple P
                 (Read x e)
                 (fun l =>
                    Exists v' : value,
                          P (locals_upd x v' l)
                    //\\  embed (locals_get x l = v (locals_upd x v' l))).

(** Write **)
Parameter Write : iexpr -> iexpr -> icmd.

Axiom Write_rule
: forall G (P Q : lprop) p v,
    G |-- embed (P |-- Exists v', ap (T := Fun locals) (ap (pure PtsTo) (eval_iexpr p)) (pure v') ** Q) ->
    G |-- triple P
           (Write p v)
           (ap (T := Fun locals) (ap (pure PtsTo) (eval_iexpr p)) (eval_iexpr v) ** Q).

(** Continuation Rules **)
(** Seq_rule **)
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
  admit.
Qed.

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
  3: eassumption. admit. eassumption.
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
  intros. eapply Conseq_rule. 3: eapply Write_rule. 2: eassumption. 2: eassumption. admit.
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
  intros. eapply Seq_rule. eapply Assert_rule. eassumption. eassumption.
Qed.

Theorem Assert_tail_rule
: forall G P Q A,
    G |-- embed (P |-- A) ->
    G |-- embed (A |-- Q) ->
    G |-- triple P (Assert A) Q.
Proof.
  intros. eapply Conseq_rule; try eassumption.
  eapply Assert_rule. admit.
Qed.





(** While **)
Parameter While : iexpr -> icmd -> icmd.

Axiom While_rule
: forall G (P Q I : lprop) t c,
    G |-- embed (P |-- I) ->
    G |-- triple (I //\\ exprProp (fun v => v <> 0) (eval_iexpr t)) c I ->
    G |-- embed (I //\\ exprProp (fun v => v = 0) (eval_iexpr t) |-- Q) ->
    G |-- triple P (While t c) Q.


Parameter WhileI : lprop -> iexpr -> icmd -> icmd.

Axiom WhileI_rule
: forall G (P Q I : lprop) t c,
    G |-- embed (P |-- I) ->
    G |-- triple (I //\\ exprProp (fun v => v <> 0) (eval_iexpr t)) c I ->
    G |-- embed (I //\\ exprProp (fun v => v = 0) (eval_iexpr t) |-- Q) ->
    G |-- triple P (WhileI I t c) Q.

(*
(** Theorem, some manipulation **)
Axiom liftEx
: forall (t : Type) G P (Q : lprop),
    G |-- @lexists _ _ t (fun v => embed (P v |-- Q)) ->
    G |-- embed (@lexists _ _ t P |-- Q).
*)



(**
(** Function Calls **)

Definition function_name := string.

Parameter Call : function_name -> iexpr -> icmd.

Axiom function_spec : function_name -> (nat -> lprop) -> (nat -> lprop) -> SProp.

Axiom Call_rule
: forall G (P Q : lprop) (P' Q' : nat -> lprop) F f e v,
    G |-- embed (P |-- ap (T := Fun locals) (ap (pure PtsTo) (eval_iexpr e)) v ** ltrue) ->
    G |-- function_spec f P' Q' -> (** Get the method spec **)
    G |-- embed (P |-- ap (T := Fun locals) (fun l v => P' v l) v ** F) -> (* P |- P' ** F *)
    G |-- embed (ap (T := Fun locals) (fun l v => Q' v l) v ** F |-- Q) -> (* Q' ** F |- Q *)
    G |-- triple P
                 (Call f e)
                 Q.
**)

Require Import Coq.Strings.String.
Local Open Scope string_scope.


Lemma embed_ltrue
: forall (P : Prop),
    P ->
    |-- @embed Prop SProp _ P.
Admitted.
Lemma locals_get_locals_upd
: forall v val m,
    locals_get v (locals_upd v val m) = val.
Admitted.
Lemma eval_iexpr_iPlus
: forall a b m,
    eval_iexpr (iPlus a b) m = eval_iexpr a m + eval_iexpr b m.
Admitted.
Lemma eval_iexpr_iVar
: forall a m,
    eval_iexpr (iVar a) m = locals_get a m.
Admitted.
Lemma eval_iexpr_iConst
: forall a m,
    eval_iexpr (iConst a) m = a.
Admitted.

Axiom pull_embed_hyp
: forall (P : Prop) (Q R : HProp),
    (P -> (Q |-- R)) ->
    Q //\\ embed P |-- R.
Axiom pull_embed_last_hyp
: forall (P : Prop) (R : HProp),
    (P -> |-- R) ->
    embed P |-- R.
*)