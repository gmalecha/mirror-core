(* This file is essentially the ILogic interface in the Charge! library.
 *   https://github.com/jesper-bengtson/Charge!
 * It is included here to avoid pulling in dependencies only for the
 * examples.
 *)
Require Import Coq.Setoids.Setoid.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Set Printing Universes.

(* NOTE: Using [Reflexive] and [Transitive] breaks universe polymorphism here
 * because [Reflexive] and [Transitive] are not universe polymorphic.
 *)

(* Logical connectives *)
Section ilogic.
  Polymorphic Universes T L.
  Polymorphic Context {L : Type@{L}}.

  Polymorphic Class ILogicOps : Type :=
  { lentails: L -> L -> Prop
  ; ltrue: L
  ; lfalse: L
  ; limpl: L -> L -> L
  ; land: L -> L -> L
  ; lor: L -> L -> L
  ; lforall: forall {T : Type@{T}}, (T -> L) -> L
  ; lexists: forall {T : Type@{T}}, (T -> L) -> L
  }.

  (* These notations have to sit strictly between level 80 (precendence of /\)
   and level 70 (precedence of =). *)
  Infix "|--"  := lentails (at level 80, no associativity).
  Infix "//\\"   := land (at level 75, right associativity).
  Infix "\\//"   := lor (at level 76, right associativity).
  Infix "-->>"   := limpl (at level 77, right associativity).
  Notation "'Forall' x : T , p" :=
    (lforall (fun x : T => p)) (at level 78, x ident, right associativity).
  Notation "'Forall' x , p" :=
    (lforall (fun x => p)) (at level 78, x ident, right associativity, only parsing).
  Notation "'Exists' x : T , p" :=
    (lexists (fun x : T => p)) (at level 78, x ident, right associativity).
  Notation "'Exists' x , p" :=
    (lexists (fun x => p)) (at level 78, x ident, right associativity, only parsing).

  Polymorphic Context {IL: ILogicOps}.

  Polymorphic Class ILogic : Type :=
  { Refl_lentails :> Reflexive lentails
  ; Trans_lentails :> Transitive lentails
  ; ltrueR: forall (C : L), C |-- ltrue
  ; lfalseL: forall (C : L), lfalse |-- C
  ; lforallL: forall (T : Type@{T}) x (P: T -> L) C, P x |-- C -> lforall P |-- C
  ; lforallR: forall (T : Type@{T}) (P: T -> L) C, (forall x, C |-- P x) -> C |-- lforall P
  ; lexistsL: forall (T : Type@{T}) (P: T -> L) C, (forall x, P x |-- C) -> lexists P |-- C
  ; lexistsR: forall (T : Type@{T}) (x : T) (P: T -> L) C, C |-- P x -> C |-- lexists P
  ; landL1: forall (P Q C : L), P |-- C  ->  P //\\ Q |-- C
  ; landL2: forall (P Q C : L), Q |-- C  ->  P //\\ Q |-- C
  ; lorR1:  forall (P Q C : L), C |-- P  ->  C |-- P \\// Q
  ; lorR2:  forall (P Q C : L), C |-- Q  ->  C |-- P \\// Q
  ; landR:  forall (P Q C : L), C |-- P  ->  C |-- Q  ->  C |-- P //\\ Q
  ; lorL:   forall (P Q C : L), P |-- C  ->  Q |-- C  ->  P \\// Q |-- C
  ; landAdj: forall (P Q C : L), C |-- (P -->> Q) -> C //\\ P |-- Q
  ; limplAdj: forall (P Q C : L), C //\\ P |-- Q -> C |-- (P -->> Q)
  }.

  Polymorphic Definition lequiv P Q := P |-- Q /\ Q |-- P.
End ilogic.

Arguments ILogicOps L : rename, clear implicits.
Arguments ILogic _ {ILOps} : rename, clear implicits.
Arguments lforallL {_ _ _ _ _ _ _} _ : rename, clear implicits.
Arguments lexistsR {_ _ _ _} _ {_ _} _ : rename, clear implicits.

Infix "|--"  := lentails (at level 80, no associativity).
Infix "//\\"   := land (at level 75, right associativity).
Infix "\\//"   := lor (at level 76, right associativity).
Infix "-->>"   := limpl (at level 77, right associativity).
Notation "'Forall' x : T , p" :=
  (lforall (fun x : T => p)) (at level 78, x ident, right associativity).
Notation "'Forall' x , p" :=
  (lforall (fun x => p)) (at level 78, x ident, right associativity, only parsing).
Notation "'Exists' x : T , p" :=
  (lexists (fun x : T => p)) (at level 78, x ident, right associativity).
Notation "'Exists' x , p" :=
  (lexists (fun x => p)) (at level 78, x ident, right associativity, only parsing).

Infix "-|-"  := lequiv (at level 85, no associativity).

Notation "|--  P" := (ltrue |-- P) (at level 85, no associativity).
Hint Extern 0 (?x |-- ?x) => reflexivity.
Hint Extern 0 (_ |-- ltrue) => apply ltrueR.
Hint Extern 0 (lfalse |-- _) => apply lfalseL.
Hint Extern 0 (?P |-- ?Q) => (is_evar P; reflexivity) || (is_evar Q; reflexivity).

Section ILogicEquiv2.
  Polymorphic Context {A : Type} `{IL: ILogic A}.

  Global Polymorphic Instance lequivEquivalence : Equivalence lequiv.
  Proof.
    unfold lequiv. constructor; red.
    + split; reflexivity.
    + intuition.
    + intros P Q R [HPQ HQP] [HQR HRQ];
      split; etransitivity; eassumption.
  Qed.

End ILogicEquiv2.

Section ILogicEmbed.
  Polymorphic Universes L1 L2.
  Polymorphic Context {A : Type@{L1}} {B : Type@{L2}}.

  Polymorphic Class EmbedOp : Type := { embed : A -> B }.

  Polymorphic Universes T.
  Polymorphic Context {ILOpsA: ILogicOps@{T L1} A}
                      {ILOpsB: ILogicOps@{T L2} B}.

  Polymorphic Class Embed {EmbOp: EmbedOp} : Type :=
  { embed_sound p q : p |-- q -> embed p |-- embed q
  ; embedlforall : forall (T : Type@{T}) f,
      Forall x : T, embed (f x) -|- embed (Forall x : T, f x)
  ; embedlexists : forall (T : Type@{T}) f,
      Exists x : T, embed (f x) -|- embed (Exists x : T, f x)
  ; embedImpl a b : (embed a) -->> (embed b) -|- embed (a -->> b)
  }.
End ILogicEmbed.

Arguments EmbedOp _ _ : clear implicits.
Arguments Embed _ _ {_ _ _} : clear implicits.

(** Basic Instances **)

Global Polymorphic Instance ILogicOps_Prop
: ILogicOps Prop := {
  lentails P Q := (P : Prop) -> Q;
  ltrue        := True;
  lfalse       := False;
  limpl    P Q := P -> Q;
  land     P Q := P /\ Q;
  lor      P Q := P \/ Q;
  lforall  T F := forall x:T, F x;
  lexists  T F := exists x:T, F x
}.

Global Polymorphic Instance ILogic_Prop : ILogic Prop.
Proof. split; cbv; firstorder. Qed.

Section functional_ilogic.
  Polymorphic Universes T T' L.
  Polymorphic Context (D : Type@{T'}) (C : Type@{L}) {ILO : ILogicOps@{T L} C}.

  Global Polymorphic Instance ILogicOps_Fun
  : ILogicOps@{T L} (D -> C) :=
  { lentails P Q := forall x : D, P x |-- Q x
  ; ltrue        := fun x => ltrue
  ; lfalse       := fun x => lfalse
  ; land     P Q := fun x => land (P x) (Q x)
  ; lor      P Q := fun x => lor (P x) (Q x)
  ; limpl    P Q := fun x => limpl (P x) (Q x)
  ; lforall  T P := fun x => lforall (fun y : T => P y x)
  ; lexists  T P := fun x => lexists (fun y : T => P y x)
  }.
  Polymorphic Context {IL : ILogic@{T L} C}.

  Global Polymorphic Instance ILogic_Fun
  : ILogic (D -> C).
  Proof.
    constructor; red; simpl; intros.
    - eapply Refl_lentails.
    - eapply Trans_lentails ; [ eapply H | eapply H0 ].
    - eapply ltrueR.
    - eapply lfalseL.
    - eapply lforallL. eapply H.
    - eapply lforallR. intros; eapply H.
    - eapply lexistsL; intros; eapply H.
    - eapply lexistsR; intros; eapply H.
    - eapply landL1; eapply H.
    - eapply landL2; eapply H.
    - eapply lorR1; eapply H.
    - eapply lorR2; eapply H.
    - eapply landR; [ eapply H | eapply H0 ].
    - eapply lorL; [ eapply H | eapply H0 ].
    - eapply landAdj; eapply H.
    - eapply limplAdj; eapply H.
  Qed.
End functional_ilogic.

Section refl_embed.
  Polymorphic Universe L.
  Context {T : Type@{L}}.
  Global Polymorphic Instance EmbedOp_refl : EmbedOp@{L L} T T :=
  { embed P := P }.

  Polymorphic Universe T.
  Polymorphic Context {ILOT : ILogicOps@{T L} T} {ILT : ILogic@{T L} T}.
  Global Polymorphic Instance Embed_refl : Embed@{L L T} T T.
  Proof.
    constructor.
    - intros. apply H.
    - unfold embed. reflexivity.
    - unfold embed. reflexivity.
    - unfold embed. reflexivity.
  Qed.
End refl_embed.

Section fun_embed.
  Context {T} {ILOT : ILogicOps T} {ILT : ILogic T}.
  Context {U} {ILOU : ILogicOps U} {ILU : ILogic U}.
  Context {EOTU : EmbedOp T U} {ETU : Embed T U}.

  Axiom embed_drop : forall (P : U) (Q : T),
      |-- Q ->
      P |-- embed Q.

  Global Instance EmbedOp_Fun {V} : EmbedOp T (V -> U) :=
  { embed P := fun _ => embed P }.
  Global Instance Embed_Fun {V} : Embed T (V -> U).
  Proof.
    constructor.
    - unfold embed; simpl. intros.
      eapply embed_sound; eauto.
    - unfold embed; simpl; intros.
      split; red; simpl; intros; eapply embedlforall.
    - unfold embed; simpl; intros.
      split; red; simpl; intros; eapply embedlexists.
    - unfold embed; simpl; intros.
      split; red; simpl; intros; eapply embedImpl.
  Qed.

End fun_embed.