Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Relations.Relations.
(*?Require Import ExtLib.Recur.Relation.
Require Import ExtLib.Recur.GenRec.
Require Import ExtLib.Tactics.
*)

Set Implicit Arguments.
Set Strict Implicit.
Set Universe Polymorphism.

Polymorphic Class Arrow@{U} (A : Type@{U} -> Type@{U} -> Type@{U}) : Type :=
{ arr : forall {T U : Type@{U}}, (T -> U) -> A T U
; acompose : forall {T U V : Type@{U}}, A T U -> A U V -> A T V
; afirst   : forall {T U V : Type@{U}}, A T U -> A (T * V)%type (U * V)%type
}.

(*
Polymorphic Class ArrowLaws A (AR : Arrow A) : Type :=
{ (*arr_id : forall {T : Type}, arr (@id T) = (@id (A T T)) *)
(* ; *)
arr_compose : forall {T U V} (f : T -> U) (g : U -> V),
    arr (fun x => g (f x)) = acompose (arr f) (arr g)
(*; first_arr : forall {T U V} (f : (T * U) -> (V * U)), afirst (arr f) = arr (fun x => (fst (f x), snd x)) *)
; first_compose : forall {T U V X} (f : A T U) (g : A U V),
    afirst (acompose f g) = acompose (afirst (V:=X) f) (afirst g)
(* *)
(* ; first_compoe_arr : acompose (afirst f) (arr fst) = acompose (arr fst) f *)
(* ; first_compose_star : acompose (afirst f) (arr (id *** g)) = acompose (arr (id *** g)) (first f) *)
(* ; first_first : acompose (afirst (afirst f)) (arr assoc) = acompose (arr assoc) (afirst f) *)
(* *)
}.
*)

Section setoid.
  Polymorphic Universe R.
  Polymorphic Universe U.
  Polymorphic Universe L.

  Variable X : Type@{U}.

  Polymorphic Definition ptrn (t : Type@{U}) : Type@{L} :=
    X -> forall T : Type@{R}, (t -> (t -> X) -> T) -> (X -> T) -> T.

  Polymorphic Definition ptrnR {t : Type@{U}} : relation (ptrn t) :=
    (eq ==>
        (fun a b => forall x,
             ((eq ==> eq) ==> (eq ==> eq) ==> eq) (a x) (b x)))%signature.

  Polymorphic Definition Succeeds {t : Type@{U}} e (m : ptrn t) val : Prop :=
    exists res, res val = e /\ forall (T : Type@{R}) good bad, m e T good bad = good val res.

  Polymorphic Definition Fails {t : Type@{U}} e (m : ptrn t) : Prop :=
    forall (T : Type@{R}) good bad, m e T good bad = bad e.

  Polymorphic Class ptrn_ok {t : Type@{U}} (p : ptrn t) : Prop :=
  { ptrn_ok_proof : forall x,
      (exists y, Succeeds x p y) \/
      (Fails x p) }.
  Arguments ptrn_ok_proof {_ _} _ _ : clear implicits.

  Polymorphic Definition run_ptrn {t : Type@{U}}
              (p : ptrn t) (default : t) (x : X) : t :=
    p x t (fun x _ => x) (fun _ => default).

  Polymorphic Theorem run_ptrn_sound
  : forall {T : Type@{U}} (P : X -> T -> Prop) (p : ptrn T) (d : T) x
           (Hpokp : ptrn_ok p),
      (Proper (eq ==> eq ==> iff) P) ->
      (forall r, Succeeds x p r -> P x r) ->
      P x d ->
      P x (run_ptrn p d x).
  Proof.
    intros.
    destruct Hpokp.
    destruct (ptrn_ok_proof0 x).
    { destruct H2.
      eapply H; [ reflexivity | | eapply H0 ]; eauto.
      red. intros.
      red in H2. destruct H2.
      exists x1.
      destruct H2.
      setoid_rewrite H3. eauto. }
    { eapply H; [ reflexivity | | eapply H1 ].
      eapply H2. }
  Qed.

  Polymorphic Definition run_ptrn_id
              (p : ptrn X) (x : X) : X :=
    p x X (fun x _ => x) (fun _ => x).

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
      p e T (fun x rebuild => good (f x) (fun y => rebuild x)) bad.

  Polymorphic Definition get : ptrn X :=
    fun e _ good _ => good e (fun e => e).

  Polymorphic Definition ignore : ptrn unit :=
    fun e _ good _ => good tt (fun _ => e).

  Polymorphic Definition pret {t : Type@{U}} (v : t) : ptrn t :=
    fun e _ good _ => good v (fun _ => e).

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

  Theorem Succeeds_pmap : forall {T U : Type@{U}} (f : T -> U) p (x : X) res,
      ptrn_ok p ->
      Succeeds x (pmap f p) res ->
      exists y, Succeeds x p y /\ res = f y.
  Proof using.
    intros. red in H0. unfold pmap in H0.
    destruct H0.
    destruct H0.
    destruct H.
    destruct (ptrn_ok_proof0 x).
    { subst.
      destruct H. exists x. split; auto.
      destruct H. destruct H.
      setoid_rewrite H0 in H1.
      specialize (H1 U (fun x _ => x) (fun _ => res)); simpl in *.
      auto. }
    { red in H. setoid_rewrite H in H1.
      specialize (H1 _ (fun _ _ => true) (fun _ => false)).
      clear - H1. inversion H1. }
  Qed.

  Theorem Succeeds_por : forall {T} p1 p2 (x : X) (res : T),
      ptrn_ok p1 -> ptrn_ok p2 ->
      Succeeds x (por p1 p2) res ->
      Succeeds x p1 res \/ Succeeds x p2 res.
  Proof.
    clear. intros.
    destruct H1 as [ ? [ ? ? ] ].
    compute in H2.
    destruct (ptrn_ok_proof H x) as [ [ ? ? ] | ].
    { left. unfold Succeeds in *.
      destruct H3 as [ ? [ ? ? ] ].
      setoid_rewrite H4.
      setoid_rewrite H4 in H2.
      specialize (H2 _ (fun x _ => x) (fun _ => x1)). simpl in H2.
      subst.
      eexists; split. 2: reflexivity. auto. }
    { right.
      unfold Succeeds, Fails in *.
      setoid_rewrite H3 in H2. eauto. }
  Qed.

  Theorem Succeeds_pfail : forall x res,
      Succeeds x pfail res ->
      False.
  Proof.
    compute. intros. destruct res.
  Qed.

  Theorem Succeeds_get : forall (x res : X),
      Succeeds x get res ->
      x = res.
  Proof.
    clear. compute. intros.
    destruct H as [ ? [ ? ? ] ].
    eapply (H0 _ (fun x _ => x)); eauto.
  Qed.

  Global Polymorphic Instance ptrn_ok_por
  : forall {T} (p1 : ptrn T) (p2 : ptrn T),
      ptrn_ok p1 -> ptrn_ok p2 -> ptrn_ok (por p1 p2).
  Proof.
    intros. constructor. intros.
    destruct (ptrn_ok_proof H x).
    { left. destruct H1. exists x0. revert H1. compute.
      intros. destruct H1 as [ ? [ ? ? ] ].
      exists x1. eauto. }
    { destruct (ptrn_ok_proof H0 x).
      { left. destruct H2. exists x0.
        unfold Succeeds, Fails in *.
        destruct H2 as [ ? [ ? ? ] ].
        compute. setoid_rewrite H1.
        eauto. }
      { right. unfold por, Fails in *.
        intros. rewrite H1. apply H2. } }
  Qed.

  Global Polymorphic Instance ptrn_ok_pmap
  : forall {T U} (p1 : ptrn T) (f : T -> U),
      ptrn_ok p1 -> ptrn_ok (pmap f p1).
  Proof.
    clear. unfold pmap.
    constructor; intros.
    destruct (ptrn_ok_proof H x).
    { destruct H0. unfold Succeeds, Fails in *.
      destruct H0 as [ ? [ ? ? ] ].
      setoid_rewrite H1. left.
      do 2 eexists. split. 2: reflexivity. assumption. }
    { unfold Succeeds, Fails in *.
      setoid_rewrite H0; eauto. }
  Qed.

  Global Polymorphic Instance ptrn_ok_get : ptrn_ok get.
  Proof.
    constructor.
    left. exists x. exists (fun x => x). compute. eauto.
  Qed.

  Global Polymorphic Instance ptrn_ok_ignore : ptrn_ok ignore.
  Proof.
    constructor.
    left. exists tt. compute. exists (fun _ => x). eauto.
  Qed.

  Global Polymorphic Instance ptrn_ok_pfail : ptrn_ok pfail.
  Proof.
    constructor.
    right. compute. reflexivity.
  Qed.

End setoid.


Polymorphic Instance Arrow_ptrn : Arrow ptrn :=
{ arr := fun T U f => fun x _T good bad => good (f x) (fun _ => x)
; acompose := fun T U V f g => fun x _T good bad =>
    f x _T (fun v rebuild_x =>
              g v _T (fun v' rebuild_x' =>
                        good v' (fun x => rebuild_x (rebuild_x' x)))
                (fun x => bad (rebuild_x x))) bad
; afirst := fun T U V f => fun x _T good bad =>
    let (a,b) := x in
    f a _T
      (fun a' rebuild_a => good (a',b) (fun p => (rebuild_a (fst p), snd p)))
      (fun a' => bad (a',b))
}.

Instance ptrn_ok_arr {T U} (f : T -> U) : ptrn_ok (arr f).
Proof.
  constructor. left. compute.
  exists (f x). exists (fun _ => x).
  eauto.
Qed.

Instance ptrn_ok_acompose {T U V : Type} p q :
  ptrn_ok p -> ptrn_ok q -> ptrn_ok (@acompose _ Arrow_ptrn T U V p q).
Proof.
  compute. intros.
  destruct H. destruct H0.
  constructor.
  intros.
  destruct (ptrn_ok_proof0 x).
  - destruct H. destruct H.
    destruct (ptrn_ok_proof1 x0).
    + left. destruct H0. exists x2.
      destruct H0.
      exists (fun x => x1 (x3 x)).
      destruct H. destruct H0.
      setoid_rewrite H1.
      setoid_rewrite H2.
      subst. eauto.
    + right. destruct H.
      red. setoid_rewrite H1. setoid_rewrite H0.
      subst. auto.
  - right. red. setoid_rewrite H. auto.
Qed.


Polymorphic Definition prod_ptrn {T U V W} (a : ptrn T U) (b : ptrn V W)
: ptrn (T*V) (U*W) :=
  fun xy _T good bad =>
    let (x,y) := xy in
    a x _T (fun a' rebuild_a =>
              b y _T (fun b' rebuild_b =>
                        good (a',b') (fun xy => (rebuild_a (fst xy), rebuild_b (snd xy))))
                (fun y => bad (rebuild_a a', y))) (fun x => bad (x, y)).

Polymorphic Definition asecond : forall {T U V : Type}, ptrn T U -> ptrn (V * T)%type (V * U)%type :=
fun T U V f => fun x _T good bad =>
    let (a,b) := x in
    f b _T
      (fun a' rebuild_a => good (a,a') (fun p => (fst p, rebuild_a (snd p))))
      (fun a' => bad (a, a')).

Require Import ExtLib.Data.POption.

Polymorphic Definition pblock {T U : Type} (p : ptrn T U) : ptrn T U :=
  fun x _T good bad =>
    match p x (poption U) (fun x _ => pSome x) (fun _ => pNone) with
    | pSome res => good res (fun _ => x)
    | pNone => bad x
    end.

Ltac prove_ptrn_ok :=
  constructor;
  match goal with
  | |- forall x : _ , _ =>
    destruct x;
    try first [ left; do 2 eexists; simpl; split;
                [ | reflexivity ]; reflexivity
              | right; compute; reflexivity ]
  end.

Lemma not_succeeds : forall T U x y z (P : Prop),
    (exists res : T -> U,  res y = z /\
                           forall X (good : T -> (T -> U) -> X) (bad : U -> X),
                             bad x = good y res) ->
    P.
Proof.
  intros. destruct H. destruct H.
  specialize (H0 _ (fun _ _ => false) (fun _ => true)).
  inversion H0.
Qed.

Ltac prove_Succeeds :=
  match goal with
  | |- Succeeds ?X _ ?d -> _ =>
    destruct X;
    try solve [ compute ; eapply not_succeeds
              | compute ;
                let H := fresh in
                destruct 1 as [ ? [ ? H ] ] ;
                specialize (H _ (fun x _ => x) (fun _ => d)) ; eauto ]
  end.


(** This is starting the example **)
Definition pcons {A} : ptrn (list A) (A * list A)%type :=
  fun x _T good bad =>
    match x with
    | nil => bad nil
    | cons x xs => good (x, xs) (fun ab => cons (fst ab) (snd ab))
    end.

Definition pnil {A} : ptrn (list A) unit :=
  fun x _T good bad =>
    match x with
    | nil => good tt (fun x => nil)
    | cons x xs => bad (cons x xs)
    end.

Instance ptrn_ok_pnil {A} : ptrn_ok (@pnil A).
Proof. prove_ptrn_ok. Qed.

Theorem Succeeds_pnil {T} (x : list T) r : Succeeds x pnil r -> x = nil.
Proof. prove_Succeeds. Qed.

Theorem ptrn_ok_pcons {A} : ptrn_ok (@pcons A).
Proof. prove_ptrn_ok. Qed.

Theorem Succeeds_pcons {T} (x : list T) r
  : Succeeds x pcons r ->
    exists a b, x = cons a b /\ (a,b) = r.
Proof. prove_Succeeds. Qed.

Definition length_2_list {A} : ptrn (list A) (A * A)%type :=
  Eval compute in
    pmap (fun a => (fst a, fst (snd a)))
         (acompose pcons (prod_ptrn (@get _) pcons)).


(**
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
**)