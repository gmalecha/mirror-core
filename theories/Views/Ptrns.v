Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relations.
Require Import ExtLib.Recur.Relation.
Require Import ExtLib.Recur.GenRec.
Require Import ExtLib.Tactics.

Set Implicit Arguments.
Set Strict Implicit.

Section setoid.
  Definition M p t := forall T, (t -> T) -> (p -> T) -> T.

  Definition Mret {p t} (v : t) : M p t :=
    fun _ good _ => good v.

  Definition Mfail {p t} (v : p) : M p t :=
    fun _ _ bad => bad v.

  Definition Mprod {p t u} (ma : M p t) (mb : M p u)
  : M p (t * u) :=
    fun _T good bad =>
      @ma _T (fun t => @mb _T (fun u => good (t,u)) bad) bad.

  Definition Mmap {p t u} (f : t -> u) (m : M p t) : M p u :=
    fun _T good bad =>
      m _T (fun x => good (f x)) bad.

  Definition ptrn (X : Type) (t : Type) : Type :=
    X -> M X t.

  Definition Mt t := forall T, (t -> T) -> T.

  Definition tptrn X (t : Type) : Type :=
    X -> Mt t.

  Definition por {X t} (l r : ptrn X t) : ptrn X t :=
    fun e T good bad =>
      l e T good (fun x => r x T good bad).

  Definition pmap {X t u} (f : t -> u) (p : ptrn X t) : ptrn X u :=
    fun e T good bad =>
      p e T (fun x => good (f x)) bad.

  Definition get {X} : ptrn X X :=
    fun e _ good _ => good e.

  Definition ignore {X} : ptrn X unit :=
    fun e _ good _ => good tt.

  Definition pret {X t} (v : t) : ptrn X t :=
    fun e _ good _ => good v.

  Definition ptret {X t} (v : t) : tptrn X t :=
    fun e _ good => good v.

  Definition pfail {X} : ptrn X Empty_set :=
    fun e _ _ bad => bad e.

  Section pors.
    Context {X T : Type}.

    Fixpoint pors (ps : list (ptrn X T)) : ptrn X T :=
      match ps with
      | nil => pmap (fun (x : Empty_set) => match x with end) pfail
      | List.cons p ps => por p (pors ps)
      end.
  End pors.

  Definition pdefault {X T} (p : ptrn X T) (d : T) : tptrn X T :=
    fun e _T good => p e _T good (fun _ => good d).

  Definition MR {T U} : relation (M T U) :=
    (fun a b => forall x,
         ((eq ==> eq) ==> (eq ==> eq) ==> eq) (a x) (b x))%signature.

  Definition ptrnR {T U} : relation (ptrn T U) :=
    (eq ==> MR)%signature.

  Definition MtR {T} : relation (Mt T) :=
    (fun a b => forall x, ((eq ==> eq) ==> eq) (a x) (b x))%signature.

  Definition tptrnR {T U} : relation (tptrn T U) :=
    (eq ==> MtR)%signature.

  Definition Succeeds {X T} e (m : ptrn X T) val : Prop :=
    forall T good bad, m e T good bad = good val.

  Definition Fails {X T} e (m : ptrn X T) : Prop :=
    forall T good bad, m e T good bad = bad e.

  Definition ptrn_ok {A B} (p : ptrn A B) : Prop :=
    forall x,
      (exists y, Succeeds x p y) \/
      (Fails x p).
  Existing Class ptrn_ok.

  Definition Mrebuild {X Y T} (f : X -> Y) (m : M X T) : M Y T :=
    fun _T good bad => m _T good (fun x => bad (f x)).

  Definition Mbind {X T U} (m1 : M X T) (m2 : T -> M X U)
  : M X U :=
    fun _T good bad =>
      m1 _T (fun x => m2 x _T good bad) bad.

  Theorem Succeeds_pmap : forall {X T U} (f : T -> U) p (x : X) res,
      ptrn_ok p ->
      Succeeds x (pmap f p) res ->
      exists y, Succeeds x p y /\ res = f y.
  Proof.
    clear.
    intros. red in H0. unfold pmap in H0.
    destruct (H x).
    { destruct H1. exists x0. split; auto.
      red in H1.
      setoid_rewrite H1 in H0.
      symmetry. eapply (H0 _ (fun x => x)).
      eauto. }
    { red in H1. setoid_rewrite H1 in H0.
      exfalso. specialize (H0 _ (fun _ => true) (fun _ => false)); inversion H0. }
  Qed.

  Theorem Succeeds_por : forall {X T} p1 p2 (x : X) (res : T),
      ptrn_ok p1 -> ptrn_ok p2 ->
      Succeeds x (por p1 p2) res ->
      Succeeds x p1 res \/ Succeeds x p2 res.
  Proof.
    clear. intros.
    destruct (H x) as [ [ ? ? ] | ].
    { left. unfold Succeeds in *.
      intros. setoid_rewrite H2 in H1.
      rewrite H2. eauto. }
    { right.
      unfold Succeeds, Fails in *. unfold por in H1.
      setoid_rewrite H2 in H1.
      eauto. }
  Qed.

  Theorem Succeeds_pfail : forall {X : Type} x res,
      Succeeds x (@pfail X) res ->
      False.
  Proof.
    compute. intros. destruct res.
  Qed.

  Definition run_tptrn {X T} (p : tptrn X T) (x : X) : T := p x T (fun x => x).

  Theorem pdefault_sound
  : forall X T (P : X -> _ -> Prop) (p : ptrn X T) (d : T) x
           (Hpokp : ptrn_ok p),
      (Proper (eq ==> MtR ==> iff) P) ->
      (forall r, Succeeds x p r -> P x (ptret r x)) ->
      P x (ptret d x) ->
      P x (pdefault p d x).
  Proof.
    intros.
    destruct (Hpokp x).
    { destruct H2.
      eapply H; [ reflexivity | | eapply H0 ]; eauto.
      compute. intros.
      red in H2. erewrite <- H3; try reflexivity.
      eapply H2. }
    { eapply H; [ reflexivity | | eapply H1 ].
      compute; intros.
      erewrite <- H3; try reflexivity.
      eapply H2. }
  Qed.

  Definition pdefault_id {X} (p : ptrn X X) : tptrn X X :=
    fun e => pdefault p e e.

  Lemma pmap_sound {X T U} {x : X} {f : T -> U} {p : ptrn X T} {res : U}
        (HSucceeds : Succeeds x (pmap f p) res)
        (H : ptrn_ok p)
        {P : U -> Prop}
        (Hstep : forall y : T, Succeeds x p y -> P (f y)) :
    P res.
  Proof.
    apply Succeeds_pmap in HSucceeds; [|assumption].
    destruct HSucceeds as [y [H1 Heq]].
    subst; apply Hstep; assumption.
  Qed.

  Theorem Succeeds_get : forall {X} (x res : X),
      Succeeds x get res ->
      x = res.
  Proof.
    clear. compute. intros.
    eapply (H _ (fun x => x)); eauto.
  Qed.

  Global Instance ptrn_ok_por
  : forall {X T} (p1 : ptrn X T) (p2 : ptrn X T),
      ptrn_ok p1 -> ptrn_ok p2 -> ptrn_ok (por p1 p2).
  Proof.
    clear.
    intros. red. intros.
    destruct (H x).
    { left. destruct H1. exists x0. revert H1. compute.
      intros. rewrite H1. auto. }
    { destruct (H0 x).
      { left. destruct H2. exists x0.
        unfold Succeeds, Fails in *.
        intros. unfold por. rewrite H1. eauto. }
      { right. unfold por, Fails in *.
        intros. rewrite H1. apply H2. } }
  Qed.

  Global Instance ptrn_ok_pmap
  : forall {X T U} (p1 : ptrn X T) (f : T -> U),
      ptrn_ok p1 -> ptrn_ok (pmap f p1).
  Proof.
    clear. unfold pmap.
    red; intros.
    destruct (H x).
    { destruct H0. unfold Succeeds, Fails in *.
      setoid_rewrite H0. eauto. }
    { unfold Succeeds, Fails in *.
      setoid_rewrite H0; eauto. }
  Qed.

  Global Instance ptrn_ok_get : forall {X}, ptrn_ok (@get X).
  Proof.
    left. exists x. compute. reflexivity.
  Qed.

  Global Instance ptrn_ok_ignore : forall {X}, ptrn_ok (@ignore X).
  Proof.
    left. exists tt. compute. reflexivity.
  Qed.

  Global Instance ptrn_ok_pfail : forall {X}, ptrn_ok (@pfail X).
  Proof.
    right. compute. reflexivity.
  Qed.

  Instance Injective_Succeeds_por {X T} p1 p2 x res
  : ptrn_ok p1 -> ptrn_ok p2 -> Injective (Succeeds x (por p1 p2) res) :=
  { result := _
  ; injection := @Succeeds_por X T _ _ _ _ _ _ }.

  Instance Injective_Succeeds_pmap {X T U} f p x res
  : ptrn_ok p -> Injective (Succeeds x (pmap f p) res) :=
  { result := _
  ; injection := @Succeeds_pmap X T U _ _ _ _ _ }.

  Instance Injective_Succeeds_get X x res
  : Injective (Succeeds x (@get X) res) :=
  { result := _
  ; injection := @Succeeds_get _ _ _ }.

(*
  Ltac drive_Succeeds :=
    let tc := eauto 100 with typeclass_instances in
    repeat match goal with
           | H : Succeeds _ (por _ _) _ |- _ =>
             eapply Succeeds_por in H ; [ destruct H | clear H ; tc | clear H ; tc ]
           | H : Succeeds _ (pmap _ _) _ |- _ =>
             eapply Succeeds_pmap in H ; [ destruct H as [ ? [ ? ? ] ] ; subst | clear H ; tc ]
           | H : Succeeds _ (inj _) _ |- _ =>
             eapply Succeeds_inj in H ; [ destruct H as [ ? [ ? ? ] ] ; subst | clear H ; tc ]
           | H : Succeeds _ (app _ _) ?X |- _ =>
             eapply Succeeds_app in H ;
               [ destruct H as [ ? [ ? [ ? [ ? ? ] ] ] ] ; subst ;
                 try (is_var X; destruct X; simpl in * )
               | clear H ; tc
               | clear H ; tc ]
           | H : Succeeds _ get _ |- _ =>
             eapply Succeeds_get in H ; subst
           end.
*)

Class SucceedsE {X T : Type} (f : X) (p : ptrn X T) (v : T) := {
  s_result : Prop;
  s_elim : Succeeds f p v -> s_result
}.

Global Instance pmap_SucceedsE {X T U : Type} {x : X} {f : T -> U} {p : ptrn X T} {res : U}
         {pok : ptrn_ok p} :
  SucceedsE x (pmap f p) res := {
  s_result := exists y, Succeeds x p y /\ res = f y;
  s_elim := Succeeds_pmap pok
}.

Global Instance por_SucceedsE {X T : Type} {x : X}  {p q : ptrn X T} {res : T}
         {pok_p : ptrn_ok p} {pok_q : ptrn_ok q} :
  SucceedsE x (por p q) res := {
  s_result := Succeeds x p res \/ Succeeds x q res;
  s_elim := Succeeds_por pok_p pok_q
}.

Global Instance get_SucceedsE {X : Type} {x res : X} :
  SucceedsE x get res := {
  s_result := x = res;
  s_elim := @Succeeds_get X x res
}.

Global Instance ignore_SucceedsE {X : Type} {x : X} (res : unit) :
  SucceedsE x ignore res := {
  s_result := res = tt;
  s_elim :=
    fun _ => match res as x return (x = tt) with
               | tt => eq_refl
             end
}.


  Definition run_default {X T} (p : ptrn X T) (def : T) (x : X) : T :=
    Eval compute in run_tptrn (pdefault p def) x.

  Theorem run_default_sound
  : forall {X T} (P : X -> T -> Prop) (p : ptrn X T) (d : T) x,
      ptrn_ok p ->
      (forall res,
          Succeeds x p res ->
          P x res) ->
      P x d ->
      P x (run_default p d x).
  Proof using.
    intros.
    change (@run_default X T) with (fun p d => @run_tptrn X T (pdefault p d)).
    unfold run_tptrn.
    unfold pdefault.
    destruct (H x).
    { destruct H2. red in H2.
      rewrite H2. auto. }
    { red in H2. rewrite H2. auto. }
  Qed.

  Section Anyof.
    Context {T : Type}.
    Variable (P : T -> Prop).

    Fixpoint Anyof (ls : list T) : Prop :=
      match ls with
      | List.nil => False
      | List.cons l ls => P l \/ Anyof ls
      end.
  End Anyof.

  Global Instance ptrn_ok_pors : forall {X T} (ps : list (ptrn X T)),
      List.Forall ptrn_ok ps ->
      ptrn_ok (pors ps).
  Proof.
    induction 1; simpl; intros; eauto with typeclass_instances.
  Qed.

  Theorem Succeeds_pors : forall {X T} ps (x : X) (res : T),
      List.Forall ptrn_ok ps ->
      Succeeds x (pors ps) res ->
      Anyof (fun p => Succeeds x p res) ps.
  Proof.
    induction 1; simpl; intros.
    { eapply Succeeds_pmap in H; eauto with typeclass_instances.
      destruct H. destruct x0. }
    { eapply Succeeds_por in H1; eauto with typeclass_instances.
      destruct H1; auto. }
  Qed.

  Global Instance pors_SucceedsE {X : Type} {x : X} (res : unit) ps
         (Hoks : List.Forall ptrn_ok ps)
  : SucceedsE x (pors ps) res :=
  { s_result := Anyof (fun p => Succeeds x p res) ps
  ; s_elim := Succeeds_pors Hoks
  }.

End setoid.

Ltac ptrn_elim :=
  repeat
   match goal with
   | H:Succeeds ?f ?p ?v
     |- _ =>
         let z := constr:(_:SucceedsE f p v) in
         apply s_elim in H; do 2 red in H; destruct_ands H
   end.

Ltac ptrn_contradict :=
  match goal with
  | H : forall (x : _), forall y, forall z, z _ = y _ |- _ =>
    exfalso; clear - H;
    specialize (H _ (fun _ => true) (fun _ => false)); simpl in H; congruence
  | H : forall (x : _), forall y, forall z, y _ = z _ |- _ =>
    exfalso; clear - H;
    specialize (H _ (fun _ => true) (fun _ => false)); simpl in H; congruence
  end.
