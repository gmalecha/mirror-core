Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Relations.Relations.
Require Import ExtLib.Recur.Relation.
Require Import ExtLib.Recur.GenRec.
Require Import ExtLib.Tactics.

Set Implicit Arguments.
Set Strict Implicit.
Set Universe Polymorphism.

Section setoid.
  Set Printing Universes.

  Polymorphic Universe R.
  Polymorphic Universe U.
  Polymorphic Universe L.

  Variable X : Type@{U}.

  Polymorphic Definition M (t : Type@{U}) : Type@{L}
    := forall T : Type@{R}, (t -> T) -> (X -> T) -> T.

  Polymorphic Definition Mret {t : Type@{U}} (v : t) : M t :=
    fun _ good _ => good v.

  Polymorphic Definition Mfail {t : Type@{U}} (v : X) : M t :=
    fun _ _ bad => bad v.

  Polymorphic Definition Mmap {t u : Type@{U}} (f : t -> u) (m : M t) : M u :=
    fun _T good bad =>
      m _T (fun x => good (f x)) bad.

  Polymorphic Definition ptrn (t : Type@{U}) : Type@{L} :=
    X -> M t.

  Polymorphic Definition MR {t : Type@{U}} : relation (M t) :=
    (fun a b => forall x,
         ((eq ==> eq) ==> (eq ==> eq) ==> eq) (a x) (b x))%signature.

  Polymorphic Definition ptrnR {t : Type@{U}} : relation (ptrn t) :=
    (eq ==> MR)%signature.

  Polymorphic Definition Succeeds {t : Type@{U}} e (m : ptrn t) val : Prop :=
    forall (T : Type@{R}) good bad, m e T good bad = good val.

  Polymorphic Definition Fails {t : Type@{U}} e (m : ptrn t) : Prop :=
    forall (T : Type@{R}) good bad, m e T good bad = bad e.

  Polymorphic Definition ptrn_ok {t : Type@{U}} (p : ptrn t) : Prop :=
    forall x,
      (exists y, Succeeds x p y) \/
      (Fails x p).
  Existing Class ptrn_ok.

  Polymorphic Definition run_ptrn {t : Type@{U}}
              (p : ptrn t) (default : t) (x : X) : t :=
    p x t (fun x => x) (fun _ => default).

  Polymorphic Theorem run_ptrn_sound
  : forall {T : Type@{U}} (P : X -> T -> Prop) (p : ptrn T) (d : T) x
           (Hpokp : ptrn_ok p),
      (Proper (eq ==> eq ==> iff) P) ->
      (forall r, Succeeds x p r -> P x r) ->
      P x d ->
      P x (run_ptrn p d x).
  Proof.
    intros.
    destruct (Hpokp x).
    { destruct H2.
      eapply H; [ reflexivity | | eapply H0 ]; eauto. }
    { eapply H; [ reflexivity | | eapply H1 ].
      eapply H2. }
  Qed.

  Polymorphic Definition run_ptrn_id
              (p : ptrn X) (x : X) : X :=
    p x X (fun x => x) (fun _ => x).

  Polymorphic Theorem run_ptrn_id_sound
  : forall (P : X -> X -> Prop) (p : ptrn X) x
           (Hpokp : ptrn_ok p),
      (Proper (eq ==> eq ==> iff) P) ->
      (forall r, Succeeds x p r -> P x r) ->
      P x x ->
      P x (run_ptrn_id p x).
  Proof.
    intros. change (run_ptrn_id p x) with (run_ptrn p x x).
    eapply run_ptrn_sound; assumption.
  Qed.

  Polymorphic Definition por {t : Type@{U}} (l r : ptrn t) : ptrn t :=
    fun e T good bad =>
      l e T good (fun x => r x T good bad).

  Polymorphic Definition pmap {t u : Type@{U}} (f : t -> u) (p : ptrn t)
  : ptrn u :=
    fun e T good bad =>
      p e T (fun x => good (f x)) bad.

  Polymorphic Definition get : ptrn X :=
    fun e _ good _ => good e.

  Polymorphic Definition ignore : ptrn unit :=
    fun e _ good _ => good tt.

  Polymorphic Definition pret {t : Type@{U}} (v : t) : ptrn t :=
    fun e _ good _ => good v.

  Polymorphic Definition pfail : ptrn Empty_set :=
    fun e _ _ bad => bad e.

  Section pors.
    Context {T : Type@{U}}.

    Polymorphic Fixpoint pors (ps : list (ptrn T)) : ptrn T :=
      match ps with
      | nil => pmap (fun (x : Empty_set) => match x with end) pfail
      | cons p ps => por p (pors ps)
      end.
  End pors.

  Polymorphic Definition Mbind {T U : Type@{U}} (m1 : M T) (m2 : T -> M U)
  : M U :=
    fun _T good bad =>
      m1 _T (fun x => m2 x _T good bad) bad.


  Theorem Succeeds_pmap : forall {T U : Type@{U}} (f : T -> U) p (x : X) res,
      ptrn_ok p ->
      Succeeds x (pmap f p) res ->
      exists y, Succeeds x p y /\ res = f y.
  Proof using.
    intros. red in H0. unfold pmap in H0.
    destruct (H x).
    { destruct H1. exists x0. split; auto.
      red in H1.
      setoid_rewrite H1 in H0.
      symmetry. eapply (H0 U (fun x => x)).
      eauto. }
    { red in H1. setoid_rewrite H1 in H0.
      exfalso. specialize (H0 _ (fun _ => true) (fun _ => false)); inversion H0. }
  Qed.

  Theorem Succeeds_por : forall {T} p1 p2 (x : X) (res : T),
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

  Theorem Succeeds_pfail : forall x res,
      Succeeds x pfail res ->
      False.
  Proof.
    compute. intros. destruct res.
  Qed.

  Lemma pmap_sound {T U} {x : X} {f : T -> U} {p : ptrn T} {res : U}
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

  Theorem Succeeds_get : forall (x res : X),
      Succeeds x get res ->
      x = res.
  Proof.
    clear. compute. intros.
    eapply (H _ (fun x => x)); eauto.
  Qed.

  Global Polymorphic Instance ptrn_ok_por
  : forall {T} (p1 : ptrn T) (p2 : ptrn T),
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

  Global Polymorphic Instance ptrn_ok_pmap
  : forall {T U} (p1 : ptrn T) (f : T -> U),
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

  Global Polymorphic Instance ptrn_ok_get : ptrn_ok get.
  Proof.
    left. exists x. compute. reflexivity.
  Qed.

  Global Polymorphic Instance ptrn_ok_ignore : ptrn_ok ignore.
  Proof.
    left. exists tt. compute. reflexivity.
  Qed.

  Global Polymorphic Instance ptrn_ok_pfail : ptrn_ok pfail.
  Proof.
    right. compute. reflexivity.
  Qed.


(*
  Polymorphic Definition MtR : relation Mt :=
    (fun a b => forall x, ((eq ==> eq) ==> eq) (a x) (b x))%signature.

  Polymorphic Definition tptrnR {U} : relation (tptrn U) :=
    (eq ==> MtR)%signature.

  Polymorphic Definition Mt (t : Type) : Type :=
    forall T : Type, (t -> T) -> T.

  Polymorphic Definition tptrn (t : Type) : Type :=
    X -> Mt t.

  Polymorphic Definition ptret {t : Type@{U}} (v : t) : tptrn t :=
    fun e _ good => good v.

  Polymorphic Definition pdefault {T : Type@{U}} (p : ptrn T) (d : T) : tptrn T :=
    fun e _T good => p e _T good (fun _ => good d).

  Polymorphic Definition run_tptrn {T} (p : tptrn T) (x : X) : T :=
    p x T (fun x => x).

  Theorem pdefault_sound
  : forall T (P : X -> _ -> Prop) (p : ptrn T) (d : T) x
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

  Polymorphic Definition pdefault_id (p : ptrn X) : tptrn X :=
    fun e => pdefault p e e.


  Polymorphic Definition run_default {T} (p : ptrn T) (def : T) (x : X) : T :=
    Eval compute in run_tptrn (pdefault p def) x.

  Theorem run_default_sound
  : forall {T} (P : X -> T -> Prop) (p : ptrn T) (d : T) x,
      ptrn_ok p ->
      (forall res,
          Succeeds x p res ->
          P x res) ->
      P x d ->
      P x (run_default p d x).
  Proof using.
    intros.
    change (@run_default T) with (fun p d => @run_tptrn T (pdefault p d)).
    unfold run_tptrn.
    unfold pdefault.
    destruct (H x).
    { destruct H2. red in H2.
      rewrite H2. auto. }
    { red in H2. rewrite H2. auto. }
  Qed.

*)

  Instance Injective_Succeeds_por {T} p1 p2 x res
  : ptrn_ok p1 -> ptrn_ok p2 -> Injective (Succeeds x (por p1 p2) res) :=
  { result := _
  ; injection := @Succeeds_por T _ _ _ _ _ _ }.

  Instance Injective_Succeeds_pmap {T U} f p x res
  : ptrn_ok p -> Injective (Succeeds x (pmap f p) res) :=
  { result := _
  ; injection := @Succeeds_pmap T U _ _ _ _ _ }.

  Instance Injective_Succeeds_get x res
  : Injective (Succeeds x get res) :=
  { result := _
  ; injection := @Succeeds_get _ _ }.

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

Global Polymorphic Class SucceedsE {T : Type} (f : X) (p : ptrn T) (v : T) := {
  s_result : Prop;
  s_elim : Succeeds f p v -> s_result
}.

Global Polymorphic Instance pmap_SucceedsE {T U : Type} {x : X} {f : T -> U} {p : ptrn T} {res : U}
         {pok : ptrn_ok p} :
  SucceedsE x (pmap f p) res := {
  s_result := exists y, Succeeds x p y /\ res = f y;
  s_elim := Succeeds_pmap pok
}.

Global Polymorphic Instance por_SucceedsE {T : Type} {x : X}  {p q : ptrn T} {res : T}
         {pok_p : ptrn_ok p} {pok_q : ptrn_ok q} :
  SucceedsE x (por p q) res := {
  s_result := Succeeds x p res \/ Succeeds x q res;
  s_elim := Succeeds_por pok_p pok_q
}.

Global Polymorphic Instance get_SucceedsE {x res : X} :
  SucceedsE x get res := {
  s_result := x = res;
  s_elim := @Succeeds_get x res
}.

Global Polymorphic Instance ignore_SucceedsE {x : X} (res : unit) :
  SucceedsE x ignore res := {
  s_result := res = tt;
  s_elim :=
    fun _ => match res as x return (x = tt) with
               | tt => eq_refl
             end
}.


  Section Anyof.
    Context {T : Type}.
    Variable (P : T -> Prop).

    Fixpoint Anyof (ls : list T) : Prop :=
      match ls with
      | List.nil => False
      | List.cons l ls => P l \/ Anyof ls
      end.
  End Anyof.

  Inductive _Forall (A : Type) (P : A -> Prop) : list A -> Prop :=
    _Forall_nil : _Forall P nil
  | _Forall_cons : forall (x : A) (l : list A),
      P x -> _Forall P l -> _Forall P (x :: l).

  Global Polymorphic Instance ptrn_ok_pors : forall {T} (ps : list (ptrn T)),
      _Forall ptrn_ok ps ->
      ptrn_ok (pors ps).
  Proof.
    induction 1; simpl; intros; eauto with typeclass_instances.
  Qed.

  Polymorphic Theorem Succeeds_pors : forall {T} ps (x : X) (res : T),
      _Forall ptrn_ok ps ->
      Succeeds x (pors ps) res ->
      Anyof (fun p => Succeeds x p res) ps.
  Proof.
    induction 1; simpl; intros.
    { eapply Succeeds_pmap in H; eauto with typeclass_instances.
      destruct H. destruct x0. }
    { eapply Succeeds_por in H1; eauto with typeclass_instances.
      destruct H1; auto. }
  Qed.

  Global Polymorphic Instance pors_SucceedsE {x : X} (res : unit) ps
         (Hoks : _Forall ptrn_ok ps)
  : SucceedsE x (pors ps) res :=
  { s_result := Anyof (fun p => Succeeds x p res) ps
  ; s_elim := Succeeds_pors Hoks
  }.

End setoid.


Polymorphic Definition Mrebuild@{R L U} {X Y T : Type@{U}} (f : X -> Y) (m : M@{R U L} X T)
: M@{R U L} Y T :=
  fun _T good bad => m _T good (fun x => bad (f x)).

Ltac ptrn_elim :=
  repeat
   match goal with
   | H:Succeeds ?f ?p ?v
     |- _ =>
         let z := constr:(_:SucceedsE f p v) in
         apply (@s_elim _ _ _ _ _ z) in H; do 2 red in H; destruct_ands H
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

Arguments get {_} _ _ _ _.
Arguments ignore {_} _ _ _ _.
Arguments Succeeds {X T} _ _ _ : rename.
