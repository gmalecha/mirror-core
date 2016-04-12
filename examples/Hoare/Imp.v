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
      intro. reflexivity.
  Qed.

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
