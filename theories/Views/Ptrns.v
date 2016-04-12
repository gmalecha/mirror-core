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

(** * Patterns **)
(** This file defines patterns which are essentially pattern matches on
 ** values that can operate at higher levels of abstraction. For example,
 ** you can run a pattern on an abstract type. The type of patterns is
 **   ptrn X T
 ** which pattern matches [X] producing a [T] if the matching succeds.
 **
 ** For the most part, you should use combinators to build patterns, but
 ** sometimes you need to implement them yourself. In that case, you need
 ** to prove two reasoning principles:
 ** 1) Your pattern is ok/parametric. This is captured by the type
 **         ptrn_ok p
 **    The tactic 'PtrnOk p' will generate the appropriate theorem type for
 **    your pattern. In general, you need to prove this in a somewhat manual
 **    process but type-class resolution will often discharge [ptrn_ok p]
 **    obligations when [p] is built from ok patterns.
 **
 ** 2) You also want to prove what you learn from knowing that your pattern
 **    succeeds. This is also encoded in a type class.
 **       SucceedsE e p v
 **    states that if pattern [p] succeeds when run on [e] and returns [v],
 **    then some property (expressed by s_result) is guaranteed.
 **)

(** TODO(gmalecha): Move to ExtLib **)
Section Anyof.
  Context {T : Type}.
  Variable (P : T -> Prop).

  Fixpoint Anyof (ls : list T) : Prop :=
    match ls with
    | List.nil => False
    | List.cons l ls => P l \/ Anyof ls
    end.
End Anyof.


Section setoid.
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
*)

  Global Polymorphic Class SucceedsE {T : Type} (f : X) (p : ptrn T) (v : T) :=
  { s_result : Prop
  ; s_elim : Succeeds f p v -> s_result
  }.

  Global Polymorphic Instance pmap_SucceedsE {T U : Type} {x : X}
         {f : T -> U} {p : ptrn T} {res : U}
         {pok : ptrn_ok p}
  : SucceedsE x (pmap f p) res :=
  { s_result := exists y, Succeeds x p y /\ res = f y
  ; s_elim := Succeeds_pmap pok
  }.

  Global Polymorphic Instance por_SucceedsE {T : Type} {x : X}  {p q : ptrn T}
         {res : T} {pok_p : ptrn_ok p} {pok_q : ptrn_ok q}
  : SucceedsE x (por p q) res :=
  { s_result := Succeeds x p res \/ Succeeds x q res
  ; s_elim := Succeeds_por pok_p pok_q
  }.

  Global Polymorphic Instance get_SucceedsE {x res : X}
  : SucceedsE x get res :=
  { s_result := x = res
  ; s_elim := @Succeeds_get x res
  }.

  Global Polymorphic Instance ignore_SucceedsE {x : X} (res : unit)
  : SucceedsE x ignore res :=
  { s_result := res = tt
  ; s_elim :=
      fun _ => match res as x return (x = tt) with
               | tt => eq_refl
               end
  }.

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


Hint Opaque por pfail get ignore pmap pors : typeclass_instances.

Polymorphic Definition Mrebuild@{R L U} {X Y T : Type@{U}} (f : X -> Y) (m : M@{R U L} X T)
: M@{R U L} Y T :=
  fun _T good bad => m _T good (fun x => bad (f x)).

Local Ltac make_type p :=
  lazymatch type of p with
  | ptrn ?F ?T -> ?rest =>
    refine (forall x : ptrn F T,
               @ptrn_ok F T x ->
               let mt := p x in
               ltac:(make_type mt))
  | forall x : ?T, _ =>
    refine (forall x : T,
               let mt := p x in
               ltac:(make_type mt))
  | ptrn _ _ => refine (ptrn_ok p)
  end.

(** * Tactic for Building the type of ptrn_ok proofs **)
Ltac PtrnOk p :=
  let x := constr:(ltac:(make_type p)) in
  let x' := eval cbv zeta in x in
  refine x'.

Ltac ptrn_elim :=
  repeat
   match goal with
   | H:Succeeds ?f ?p ?v
     |- _ =>
         let z := constr:(ltac:(eauto 100 with typeclass_instances) : SucceedsE f p v) in
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


(** TODO: There should be a general proof for this *)
Ltac solve_ok :=
  let do_it H :=
      let x := fresh in
      intro x; destruct x; simpl; try solve [ right; compute; reflexivity ] ;
      match goal with
      | H' : _ |- _ =>
        lazymatch H' with
        | H => fail 2
        | _ =>
          let H'' := fresh in
          let x'' := fresh in
          destruct (H H') as [ [ x'' H'' ] | H'' ] ;
          [ left ; exists x'' ; try solve [ compute ; intros; eapply H'' ]
          | right ; try solve [ compute; intros; eapply H'' ] ]
        end
      end
  in
  intros;
  match goal with
  | H : ptrn_ok ?X |- ptrn_ok (_ ?X) => do_it H
  | |- ptrn_ok _ =>
    let x := fresh in
    intro x; destruct x; simpl; auto;
    try solve [ right; compute; reflexivity
              | left; eexists; compute; reflexivity ]
  end.

Definition Mtwo {T U V W X} (f : T -> U -> X)
           (p1 : ptrn T V) (p2 : V -> ptrn U W)
           (x1 : T) (x2 : U) : M X W :=
  fun _T good bad =>
    p1 x1 _T (fun v => p2 v x2 _T good (fun u => bad (f x1 u)))
       (fun t => bad (f t x2)).
Definition Myes {X T} (m : M X T) res : Prop :=
  forall T good bad, m T good bad = good res.
Definition Mno {X T} (m : M X T) x : Prop :=
  forall T good bad, m T good bad = bad x.
Definition Mok {X T} (m : M X T) (x : X) : Prop :=
  (exists y, Myes m y) \/ Mno m x.
Lemma Mtwo_ok {T U V W X} f p1 p2 x1 x2
  : ptrn_ok p1 ->
    (forall v, ptrn_ok (p2 v)) ->
    Mok (@Mtwo T U V W X f p1 p2 x1 x2) (f x1 x2).
Proof.
  intros.
  destruct (H x1) as [ [ ? ? ] | ].
  - destruct (H0 x x2) as [ [ ? ? ] | ].
    + left. exists x0.
      unfold Mtwo, Succeeds in *.
      red; intros.
      rewrite H1. apply H2.
    + right. red in H1. red in H2.
      red. compute; intros.
      rewrite H1. apply H2.
  - right. red in H1.
    compute; intros. apply H1.
Qed.

Lemma Mrebuild_Succeeds : forall {X Y} (p' : ptrn X Y) {T} p f v x,
    (forall T0 (good : T -> T0) (bad : X -> T0),
        Mrebuild (X:=Y) f (p x) good bad = good v) ->
    (forall T0 good bad, p x T0 good (fun x : Y => p' (f x) T0 bad (fun _ : X => good v)) = p x T0 good bad) ->
    Succeeds x p v.
Proof.
  red. intros.
  unfold Mrebuild in *.
  specialize (H T0 good (fun x => @p' x T0 bad (fun _ => good v))).
  simpl in H.
  rewrite H0 in H. assumption.
Qed.

Lemma Mtwo_Succeeds : forall {X Y Z} (p2' : ptrn Z Y) {T T'}
                             (p1 : ptrn X T) (p2 : T -> ptrn Y T') (f : X -> Y -> Z) v arg logic,
    ptrn_ok p1 ->
    (forall T0 (good : _ -> T0) bad,
        Mtwo (X:=Z) f p1 p2 arg logic good bad = good v) ->
    (forall T0 (good : _ -> T0) bad x logic, p2 x logic T0 good
                                                (fun u : Y => p2' (f arg u) T0 bad (fun _ : Z => good v)) = p2 x logic T0 good bad) ->
    exists val,
      Succeeds arg p1 val /\ Succeeds logic (p2 val) v.
Proof.
  intros. unfold Mtwo in *.
  destruct (H arg); clear H.
  - destruct H2. exists x.
    split; auto.
    red in H. setoid_rewrite H in H0.
    red. intros. specialize (H0 T0 good).
    specialize (H0 (fun z => p2' z T0 bad (fun _ => good v))).
    simpl in H0.
    rewrite H1 in H0. assumption.
  - clear H1.
    unfold Fails in H2.
    setoid_rewrite H2 in H0.
    specialize (H0 bool (fun _ => true) (fun _ => false)). inversion H0.
Qed.

(** TODO(gmalecha): ExtLib? **)
Lemma unit_irr : forall a b : unit, a = b.
Proof. destruct a; destruct b; reflexivity. Qed.


Ltac solve_Succeeds :=
  match goal with
  | |- Succeeds ?e (?p' _ _ _ _) ?v -> _ =>
    destruct e;
    let H := fresh in
    try solve [ intro H ; specialize (H bool (fun _ => true) (fun _ => false)); inversion H
              | do 2 eexists; split; eauto;
                red in H; simpl in H ;
                eapply Mtwo_Succeeds with (p2':=p' _ _ ignore (fun _ => get)) in H; eauto ]
  | |- Succeeds ?e (?p' _ _) ?v -> _ =>
    destruct e;
    let H := fresh in
    try solve [ intro H ; specialize (H bool (fun _ => true) (fun _ => false)); inversion H
              | intros; eexists; split; auto;
                red in H; simpl in H ;
                eapply (@Mrebuild_Succeeds _ _ (p' _ get)) in H; [ auto | reflexivity ] ]
  | |- Succeeds ?e ?p' ?v -> _ =>
    destruct e;
    let H := fresh in
    try solve [ intro H ; specialize (H bool (fun _ => true) (fun _ => false)); inversion H
              | split; auto using unit_irr ]
  end.
