(** This file implements a variation on patterns that uses option or sum to
 ** encode failure. It also uses a single implementation of ptrn_ok and Succeeds.
 ** It does not contain a notion of failure.
 **)
Require Import ExtLib.Data.POption.

Require Import Coq.Lists.List.

Set Implicit Arguments.
Set Strict Implicit.
Set Universe Polymorphism.
Set Printing Universes.

Polymorphic Inductive peq@{X} {A : Type@{X}} (l : A) : A -> Prop :=
| prefl : peq l l.

Polymorphic Inductive pex@{X} {A : Type@{X}} (P : A -> Prop) : Prop :=
| pex_intro : forall x : A, P x -> pex P.

Notation "'pexists' x , y" := (@pex _ (fun x => y)) (at level 200).
Notation "'pexists' x : T , y" := (@pex T (fun x => y)) (at level 200).


Polymorphic Inductive psum@{A B} (a : Type@{A}) (b : Type@{B}) : Type :=
| pinl (_ : a) | pinr (_ : b).

Arguments pinl {_ _} _.
Arguments pinr {_ _} _.


Module Type MType.
  Section poly.
    Polymorphic Universes X T P.
    Constraint X < P.
    Constraint T < P.

    Parameter M : Type@{X} -> Type@{T} -> Type@{P}.

    Polymorphic Universe Z.
    Constraint Z < P.
    Parameter Melim : forall {X : Type@{X}} {T : Type@{T}} {U : Type@{Z}}, M X T -> (T -> U) -> U -> U.
  End poly.

  Parameter Mmap@{X A B P}
  : forall (x : Type@{X}) (t : Type@{A}) (u : Type@{B}),
      (t -> u) -> M@{X A P} x t -> M@{X B P} x u.

  Parameter Mret@{X A P} : forall {x : Type@{X}} {t : Type@{A}}, t -> M@{X A P} x t.

  Parameter Mbind@{X A B P} : forall {x : Type@{X}} {t : Type@{A}} {u : Type@{B}},
      M@{X A P} x t -> (t -> M@{X B P} x u) -> M@{X B P} x u.

  Parameter Mjoin@{X T P P'} : forall (x : Type@{X}) (t : Type@{T}),
      M@{X P' P} x (M@{X T P'} x t) -> M@{X T P} x t.

  Parameter Mfail@{X T P} : forall {x : Type@{X}} {t : Type@{T}},
      x -> M@{X T P} x t.

  Parameter Mor@{X T P} : forall (x : Type@{X}) (t : Type@{T}),
      M@{X T P} x t -> M@{X T P} x t -> M@{X T P} x t.

  Parameter Mrebuild@{X Y A P} : forall (x : Type@{X}) (y : Type@{Y}) (t : Type@{A}),
      (x -> y) -> M@{X A P} x t -> M@{Y A P} y t.

  Parameter Mok@{X T P} : forall {X : Type@{X}} {T : Type@{T}},
      (X -> Prop) -> (T -> Prop) -> M@{X T P} X T -> Prop.

  Axiom Mok_Melim@{X T P Z}
  : forall {X: Type@{X}} {T : Type@{T}} {U : Type@{Z}} (P : _ -> Prop) (Q : _ -> Prop) (R : _ -> Prop) (m : M X T) (succ : T -> U) (default : U),
      Mok P Q m ->
      (forall x, Q x -> R (succ x)) ->
      (forall x, P x -> R default) ->
      R (Melim@{X T P Z} m succ default).

  Axiom Mok_conseq@{X T P}
  : forall {X : Type@{X}} {T : Type@{T}} (P P' : X -> Prop) (Q Q' : T -> Prop) (c : M@{X T P} X T),
      Mok P Q c ->
      (forall x : X, P x -> P' x) ->
      (forall x : T, Q x -> Q' x) ->
      Mok@{X T P} P' Q' c.

  Axiom Mok_Mmap : forall x t u (f : t -> u) (P : _ -> Prop) (Q : _ -> Prop) (c : M x t),
      Mok P Q c ->
      Mok P (fun x => pexists y, peq x (f y) /\ Q y) (Mmap f c).

  Axiom Mok_Mret@{X T P} : forall {x : Type@{X}} {t : Type@{T}} (c : t),
      Mok@{X T P} (fun _ => False) (fun x => peq x c) (@Mret@{X T P} x t c).

  Axiom Mok_Mbind@{X T U P}
  : forall {x : Type@{X}} {t : Type@{T}} {u : Type@{U}}
      (P : x -> Prop) (Q : t -> Prop) (P' : t -> x -> Prop) (Q' : t -> u -> Prop)
      (c : M x t) (k : t -> M x u),
      Mok@{X T P} P Q c ->
      (forall x : t, Mok@{X U P} (P' x) (Q' x) (k x)) ->
      Mok@{X U P}
         (fun x => P x \/ pexists y, Q y /\ P' y x)
         (fun x => pexists y, Q y /\ Q' y x)
         (Mbind@{X T U P} c k).

  Axiom Mok_Mjoin@{X T P P'}
  : forall (x : Type@{X}) (t : Type@{T}) P P' Q Q' (c : M@{X P' P} x (M@{X T P'} x t)),
      Mok@{X P' P} P Q c ->
      (forall m, Q m -> Mok@{X T P'} P' Q' m) ->
      Mok (fun x => P x \/ P' x) Q' (Mjoin@{X T P P'} c).

  Axiom Mok_Mfail@{X T P} : forall (x : Type@{X}) (t : Type@{T}) (v : x),
    Mok (fun x => peq x v) (fun _ => False) (@Mfail@{X T P} x t v).

  Axiom Mok_Mor@{X T P} : forall (x : Type@{X}) (t : Type@{T})
      (l r : M@{X T P} x t) (P : x -> Prop) (Q Q' : t -> Prop),
    Mok P Q l ->
    Mok P Q' r ->
    Mok P (fun x => Q x \/ Q' x) (Mor l r).

  Axiom Mok_Mrebuild@{X Y A P}
  : forall (x : Type@{X}) (y : Type@{Y}) (t : Type@{A})
      (f : x -> y) (c : M@{X A P} x t) P Q,
      Mok P Q c ->
      Mok (fun x => pexists y, peq x (f y) /\ P y) Q (Mrebuild f c).

End MType.

Module Type PtrnsT.
  Section poly.
    Polymorphic Universes X T P.
    Constraint X < P.
    Constraint T < P.

    Parameter ptrn : forall (X : Type@{X}) (T : Type@{T}), Type@{P}.
  End poly.

  Parameter pmap@{X T U P}
  : forall {X : Type@{X}} {T : Type@{T}} {U : Type@{U}} (f : T -> U) (p : ptrn@{X T P} X T), ptrn@{X U P} X U.

  Parameter pget : forall (X : Type), ptrn X X.

  Parameter pignore@{X P} : forall {X : Type@{X}}, ptrn@{X Set P} X unit.

  Parameter pfail@{X Y P} : forall {X : Type@{X}} {Y : Type@{Y}}, ptrn@{X Y P} X Y.

  (** Specification *)
  Parameter Pok@{X T P} : forall {X : Type@{X}} {T : Type@{T}}
      (Q : X -> T -> Prop) (p : ptrn@{X T P} X T), Prop.

  (** Reasoning principles *)
  Axiom Pok_pmap@{X T U P} : forall X T U f p P,
    Pok@{X T P} P p ->
    Pok@{X U P} (fun x v => pexists y, peq v (f y) /\ P x y) (@pmap X T U f p).

  Axiom Pok_pget@{X P} : forall {T : Type@{X}}, Pok@{X X P} (@peq T) (@pget T).

  Axiom Pok_pignore@{X P} : forall {X : Type@{X}},
      Pok@{X Set P} (fun _ => @peq _ tt) (@pignore X).

  Axiom Pok_pfail@{X T P} : forall {X : Type@{X}} {Y : Type@{T}},
      Pok@{X Set P} (fun _ _ => False) (@pfail X Y).

End PtrnsT.

Module MakePtrns (P : MType) <: PtrnsT.
  Import P.

  Section poly.
    Polymorphic Universes X T P.
    Constraint X < P.
    Constraint T < P.

    Definition ptrn (X : Type@{X}) (T : Type@{T}) : Type@{P} :=
      X -> M@{X T P} X T.
  End poly.

  Definition run_ptrn {X} {T} {U} (p : ptrn X T) (succ : T -> U) (default : U) (x : X) : U :=
    Melim (p x) succ default.

  Definition pmap@{X A B P}
             {X : Type@{X}} {T : Type@{A}} {U : Type@{B}} (f : T -> U)
             (p : ptrn@{X A P} X T) : ptrn@{X B P} X U :=
    fun x => Mmap@{X A B P} f (p x).

  Definition pget@{X P} (X : Type@{X}) : ptrn@{X X P} X X :=
    @Mret _ _.

  Definition pignore@{X P} (X : Type@{X}) : ptrn@{X Set P} X unit :=
    fun _ => @Mret _ _ tt.

  Definition pfail (X Y : Type) : ptrn X Y :=
    fun x => @Mfail _ _ x.

  (** Specification *)
  Definition Pok@{X T P} {X : Type@{X}} {T : Type@{T}}
      (Q : X -> T -> Prop) (p : ptrn@{X T P} X T) : Prop :=
    forall x : X, Mok (fun y => @peq X x y) (Q x) (p x).


  Theorem run_ptrn_ok@{X T U P}
  : forall {X : Type@{X}} {T : Type@{T}} {U : Type@{U}} (p : ptrn@{X T P} X T)
      (succ : T -> U) (default : U) (x : X) P (Q : _ -> Prop),
      Pok P p ->
      (forall y, P x y -> Q (succ y)) ->
      Q default ->
      Q (run_ptrn p succ default x).
  Proof.
    simpl; intros. red in H.
    unfold run_ptrn. eapply Mok_Melim.
    eapply H. eauto. eauto.
    Show Proof.

  Qed.

  (** Reasoning principles *)
  Theorem Pok_pmap@{X T U P} {X : Type@{X}} {T : Type@{T}} {U : Type@{U}} (f : T -> U) p P
  : Pok@{X T P} P p ->
    Pok@{X U P} (fun x v => pex (fun y => peq v (f y) /\ P x y)) (@pmap X T U f p).
  Proof. compute. intros.
         eapply Mok_conseq; [ eapply Mok_Mmap; apply H | auto | ].
         simpl. destruct 1. exists x1. destruct H0. destruct H0.
         split; auto. constructor.
  Defined.

  Theorem Pok_pget@{X P} {T : Type@{X}} : Pok@{X X P} (@peq T) (@pget T).
  Proof. compute. intros.
         eapply Mok_conseq; [ eapply Mok_Mret | | ].
         { destruct 1. }
         { destruct 1; constructor. }
  Defined.

  Theorem Pok_pignore@{X P} {X : Type@{X}}
  : Pok@{X Set P} (fun _ => @peq _ tt) (@pignore@{X P} X).
  Proof. compute. intros.
         eapply Mok_conseq; [ eapply Mok_Mret | | ].
         { destruct 1. }
         { destruct 1. constructor. }
  Defined.

  Theorem Pok_pfail@{X T P} {X : Type@{X}} {Y : Type@{T}}
  : Pok@{X Set P} (fun _ _ => False) (@pfail X Y).
  Proof. compute. intros.
         eapply Mok_conseq; [ eapply Mok_Mfail | | ]; auto.
         simpl. destruct 1; constructor.
  Defined.

  Definition pap@{X T U P} {X : Type@{X}} {T : Type@{T}} {U : Type@{U}}
             (r : T -> X) (p : ptrn@{X T P} X T) (p' : ptrn@{T U P} T U) : ptrn@{X U P} X U :=
    fun e => Mbind (p e) (fun x => Mrebuild r (p' x)).

  Theorem Pok_pap@{X T U P} : forall {X : Type@{X}} {T : Type@{T}} {U : Type@{U}}
             (r : T -> X) (p : ptrn@{X T P} X T) (p' : ptrn@{T U P} T U)
             P P',
      Pok P p ->
      Pok P' p' ->
      (forall x y, P x y -> peq x (r y)) ->
      Pok (fun i o => pexists i', P i i' /\ P' i' o) (pap r p p').
  Proof.
    compute. intros.
    eapply Mok_conseq; [ eapply Mok_Mbind | | ].
    { eapply H. }
    { intros.
      eapply Mok_Mrebuild; eauto. }
    { simpl. intros.
      destruct H2; auto.
      destruct H2. destruct H2. destruct H3.
      eapply H1 in H2. symmetry in H2. destruct H2.
      destruct H3. symmetry in H2. destruct H2. destruct H3. reflexivity. }
    { simpl. destruct 1. destruct H2. eexists. split; eauto. }
  Defined.

End MakePtrns.

Require Import MirrorCore.Lambda.ExprCore.

Module LambdaP (MT : MType).
  Module P := MakePtrns MT.
  Import P.
  Import MT.

  Section with_typ_sym.
    Variable typ sym : Set.

    Definition abs@{T P} {T U : Type@{T}}
               (l : ptrn@{Set T P} typ T)
               (r : ptrn@{Set T P} (expr typ sym) U)
    : ptrn@{Set T P} (expr typ sym) (T * U) :=
      fun e =>
        match e return M@{Set T P} (expr typ sym) (T * U) with
        | Abs lv rv =>
          Mbind@{Set T T P} (Mrebuild@{Set Set T P} (fun l' => Abs l' rv) (l lv))
               (fun lv' => Mbind@{Set T T P} (Mrebuild@{Set Set T P} (Abs lv) (r rv))
                             (fun rv' => Mret@{Set T P} (lv', rv')))
        | e => Mfail@{Set T P} e
        end.

    Theorem Pok_abs@{T P} : forall (T U : Type@{T})
                              (l : ptrn@{Set T P} typ T)
                              (r : ptrn@{Set T P} (expr typ sym) U) P P',
        Pok P l ->
        Pok P' r ->
        Pok (fun i o => pexists l, pexists r,
                     i = Abs l r /\ P l (fst o) /\ P' r (snd o))
            (abs@{T P} l r).
    Proof. unfold Pok; destruct x; simpl;
             try (eapply Mok_conseq;
                  [ eapply Mok_Mfail
                  | simpl; intros; symmetry; assumption
                  | destruct 1 ]).
           eapply Mok_conseq; [ eapply Mok_Mbind | | ].
           eapply Mok_Mrebuild. eapply H.
           intros. eapply Mok_Mbind. eapply Mok_Mrebuild. eapply H0.
           intros. eapply Mok_Mret.
           { simpl. destruct 1.
             { destruct H1. destruct H1.
               destruct H2. symmetry. assumption. }
             { destruct H1. destruct H1. destruct H2.
               { destruct H2. destruct H2. destruct H3. symmetry; assumption. }
               { destruct H2. destruct H2. destruct H3. } } }
           { simpl. destruct 1 as [ ? [ ? [ ? [ ? ? ] ] ] ].
             symmetry in H3. destruct H3; simpl.
             eexists. eexists. eauto. }
    Defined.

    Definition app@{T P} {T U : Type@{T}}
               (l : ptrn@{Set T P} (expr typ sym) T)
               (r : ptrn@{Set T P} (expr typ sym) U)
      : ptrn@{Set T P} (expr typ sym) (T * U) :=
      fun e =>
        match e return M@{Set T P} (expr typ sym) (T * U) with
        | App lv rv =>
          Mbind@{Set T T P} (Mrebuild@{Set Set T P} (fun l' => App l' rv) (l lv))
               (fun lv' => Mbind@{Set T T P} (Mrebuild@{Set Set T P} (App lv) (r rv))
                             (fun rv' => Mret@{Set T P} (lv', rv')))
        | e => Mfail@{Set T P} e
        end.

    Theorem Pok_app@{T P} : forall (T U : Type@{T})
                              (l : ptrn@{Set T P} (expr typ sym) T)
                              (r : ptrn@{Set T P} (expr typ sym) U) P P',
        Pok P l ->
        Pok P' r ->
        Pok (fun i o => pexists l, pexists r,
                     i = App l r /\ P l (fst o) /\ P' r (snd o))
            (app@{T P} l r).
    Proof. unfold Pok; destruct x; simpl;
             try (eapply Mok_conseq;
                  [ eapply Mok_Mfail
                  | simpl; intros; symmetry; assumption
                  | destruct 1 ]).
           eapply Mok_conseq; [ eapply Mok_Mbind | | ].
           eapply Mok_Mrebuild. eapply H.
           intros. eapply Mok_Mbind. eapply Mok_Mrebuild. eapply H0.
           intros. eapply Mok_Mret.
           { simpl. destruct 1.
             { destruct H1. destruct H1.
               destruct H2. symmetry. assumption. }
             { destruct H1. destruct H1. destruct H2.
               { destruct H2. destruct H2. destruct H3. symmetry; assumption. }
               { destruct H2. destruct H2. destruct H3. } } }
           { simpl. destruct 1 as [ ? [ ? [ ? [ ? ? ] ] ] ].
             symmetry in H3. destruct H3; simpl.
             eexists. eexists. eauto. }
    Defined.

    Definition var@{P} : ptrn@{Set Set P} (expr typ sym) nat :=
      fun e =>
        match e with
        | Var v => Mret v
        | e => Mfail e
        end.

    Theorem Pok_var@{P} : Pok (fun i o => peq i (Var o)) var@{P}.
    Proof.
      unfold uvar.
      red; destruct x; simpl;
        try (eapply Mok_conseq;
             [ eapply Mok_Mfail
             | simpl; intros; symmetry; assumption
             | destruct 1 ]).
      eapply Mok_conseq; [ eapply Mok_Mret
                         | destruct 1
                         | destruct 1; reflexivity ].
    Defined.

    Definition uvar@{P} : ptrn@{Set Set P} (expr typ sym) nat :=
      fun e =>
        match e with
        | UVar v => Mret v
        | e => Mfail e
        end.

    Theorem Pok_uvar@{P} : Pok (fun i o => peq i (UVar o)) uvar@{P}.
    Proof.
      unfold uvar.
      red; destruct x; simpl;
        try (eapply Mok_conseq;
             [ eapply Mok_Mfail
             | simpl; intros; symmetry; assumption
             | destruct 1 ]).
      eapply Mok_conseq; [ eapply Mok_Mret
                         | destruct 1
                         | destruct 1; reflexivity ].
    Defined.

  End with_typ_sym.

End LambdaP.

Module PtrnOption <: MType.
  Section poly.
    Polymorphic Universes X T P.
    Constraint X <= P.
    Constraint T <= P.

    Definition M : Type@{X} -> Type@{T} -> Type@{P} := fun _ x => poption@{T} x : Type@{P}.

    Polymorphic Universe Z.
    Constraint Z < P.
    Definition Melim {X : Type@{X}} {T : Type@{T}} {U : Type@{Z}}
               (x : M X T) (succ : T -> U) (default : U) : U :=
      match x with
      | pNone => default
      | pSome x => succ x
      end.

  End poly.

  Definition Mmap@{X A B P} (xt : Type@{X}) (t : Type@{A}) (u : Type@{B})
             (f : t -> u) (x : M@{X A P} xt t) : M@{X B P} xt u :=
    match x with
    | pNone => pNone
    | pSome x => pSome (f x)
    end.

  Definition Mret@{X T P} : forall (x : Type@{X}) (t : Type@{T}), t -> M@{X T P} x t := fun _ => @pSome@{T}.

  Definition Mbind@{X T U P} (x : Type@{X}) (t : Type@{T}) (u : Type@{U})
             (c : M@{X T P} x t) (k : t -> M@{X U P} x u) : M@{X U P} x u :=
    match c with
    | pNone => pNone
    | pSome x => k x
    end.

  Definition Mjoin@{X T P P'} {xt : Type@{X}} {t : Type@{T}}
      (x : M@{X P' P} xt (M@{X T P'} xt t)) : M@{X T P} xt t :=
    match x with
    | pNone => pNone
    | pSome v => v
    end.

  Definition Mfail@{X T P} : forall (x : Type@{X}) (t : Type@{T}) , x -> M@{X T P} x t := fun _ _ _ => @pNone _.

  Definition Mor@{X T P} (x : Type@{X}) (t : Type@{T}) (l r : M@{X T P} x t) : M@{X T P} x t :=
    match l with
    | pNone => r
    | l => l
    end.

  Definition Mrebuild@{X Y A P} (x : Type@{X}) (y : Type@{Y}) (t : Type@{A})
             (f : x -> y) (c : M@{X A P} x t) : M@{Y A P} y t :=
    match c with
    | pNone => pNone
    | pSome y => pSome y
    end.

  Inductive pex@{T} (t : Type@{T}) (p : t -> Prop) : Prop :=
  | pex_intro : forall x : t, p x -> pex p.

  Definition Mok@{X T P} {X : Type@{X}} {T : Type@{T}}
  (fail : X -> Prop) (succ : T -> Prop) (c : M@{X T P} X T) : Prop :=
    match c return Prop with
    | pNone => pex fail
    | pSome x => succ x
    end.

  Theorem Mok_Melim@{X T P Z}
  : forall {X: Type@{X}} {T : Type@{T}} {U : Type@{Z}} (P : _ -> Prop) (Q : _ -> Prop) (R : _ -> Prop) (m : M X T) (succ : T -> U) (default : U),
      Mok P Q m ->
      (forall x, Q x -> R (succ x)) ->
      (forall x, P x -> R default) ->
      R (Melim@{X T P Z} m succ default).
  Proof.
    destruct m; simpl; eauto. intros. destruct H. eapply H1. eauto.
  Defined.

  Theorem Mok_conseq@{X T P}
  : forall {X : Type@{X}} {T : Type@{T}} (P P' : X -> Prop) (Q Q' : T -> Prop) (c : M@{X T P} X T),
      Mok P Q c ->
      (forall x : X, P x -> P' x) ->
      (forall x : T, Q x -> Q' x) ->
      Mok@{X T P} P' Q' c.
  Proof.
    destruct c; simpl; eauto.
    intros. destruct H. eexists; eauto.
  Defined.

  Theorem Mok_Mmap : forall x t u (f : t -> u) P Q (c : M x t),
      Mok P Q c ->
      Mok P (fun x => pexists y, peq x (f y) /\ Q y) (Mmap f c).
  Proof.
    destruct c; simpl; eauto. intros.
    eexists. split; eauto. reflexivity.
  Defined.

  Theorem Mok_Mret@{X T P} : forall {x : Type@{X}} {t : Type@{T}} (c : t),
      Mok@{X T P} (fun _ => False) (fun x => peq x c) (@Mret@{X T P} x t c).
  Proof.
    compute. auto. reflexivity.
  Defined.

  Theorem Mok_Mbind@{X T U P}
  : forall {x : Type@{X}} {t : Type@{T}} {u : Type@{U}}
      (P : x -> Prop) (Q : t -> Prop) (P' : t -> x -> Prop) (Q' : t -> u -> Prop) (c : M x t) (k : t -> M x u),
      Mok@{X T P} P Q c ->
      (forall x : t, Mok@{X U P} (P' x) (Q' x) (k x)) ->
      Mok@{X U P}
         (fun x => P x \/ pexists y, Q y /\ P' y x)
         (fun x => pexists y, Q y /\ Q' y x)
         (Mbind@{X T U P} c k).
  Proof.
    destruct c; simpl; eauto.
    { intros. specialize (H0 t0). destruct (k t0); simpl; eauto.
      simpl in H0. eexists; eauto.
      simpl in *. destruct H0. exists x0. right; eexists; eauto. }
    { destruct 1. unfold Mok. intros. eexists; eauto. }
  Defined.

  Theorem Mok_Mjoin@{X T P P'}
  : forall (x : Type@{X}) (t : Type@{T}) P P' Q Q' (c : M@{X P' P} x (M@{X T P'} x t)),
      Mok@{X P' P} P Q c ->
      (forall m, Q m -> Mok@{X T P'} P' Q' m) ->
      Mok (fun x => P x \/ P' x) Q' (Mjoin@{X T P P'} c).
  Proof. destruct c. simpl; auto.
         simpl. intros.
         apply H0 in H; clear - H.
         { destruct m; simpl in *; auto. destruct H; eexists; eauto. }
         { simpl. destruct 1; eexists; eauto. }
  Defined.

  Theorem Mok_Mfail@{X T P} : forall (x : Type@{X}) (t : Type@{T}) (v : x),
    Mok (fun x => peq x v) (fun _ => False) (@Mfail@{X T P} x t v).
  Proof. compute. eexists; eauto. constructor. Defined.

  Theorem Mok_Mor@{X T P} : forall (x : Type@{X}) (t : Type@{T})
      (l r : M@{X T P} x t) (P : x -> Prop) (Q Q' : t -> Prop),
    Mok P Q l ->
    Mok P Q' r ->
    Mok P (fun x => Q x \/ Q' x) (Mor l r).
  Proof. destruct l; auto. destruct r; eauto; simpl; eauto.
         simpl. intros. destruct r; simpl in *; eauto.
  Defined.

  Theorem Mok_Mrebuild@{X Y A P}
  : forall (x : Type@{X}) (y : Type@{Y}) (t : Type@{A})
      (f : x -> y) (c : M@{X A P} x t) P Q,
      Mok P Q c ->
      Mok (fun x => pexists y, peq x (f y) /\ P y) Q (Mrebuild f c).
  Proof. destruct c; simpl; eauto.
         intros. destruct H; eexists; eauto.
         eexists; split; eauto. constructor.
  Defined.

End PtrnOption.

Module PtrnEither <: MType.
  Section poly.
    Polymorphic Universes X T P.
    Constraint X <= P.
    Constraint T <= P.

    Definition M : Type@{X} -> Type@{T} -> Type@{P} := psum@{X T}.

    Polymorphic Universe Z.
    Constraint Z < P.
    Definition Melim {X : Type@{X}} {T : Type@{T}} {U : Type@{Z}}
               (x : M X T) (succ : T -> U) (default : U) : U :=
      match x with
      | pinl _ => default
      | pinr x => succ x
      end.

  End poly.

  Definition Mmap@{X A B P} (xt : Type@{X}) (t : Type@{A}) (u : Type@{B})
             (f : t -> u) (x : M@{X A P} xt t) : M@{X B P} xt u :=
    match x with
    | pinl x => pinl x
    | pinr x => pinr (f x)
    end.

  Definition Mret@{X T P} : forall (x : Type@{X}) (t : Type@{T}), t -> M@{X T P} x t := @pinr@{X T}.

  Definition Mbind@{X T U P} (x : Type@{X}) (t : Type@{T}) (u : Type@{U})
             (c : M@{X T P} x t) (k : t -> M@{X U P} x u) : M@{X U P} x u :=
    match c with
    | pinl x => pinl x
    | pinr x => k x
    end.

  Definition Mjoin@{X T P P'} {xt : Type@{X}} {t : Type@{T}}
             (x : M@{X P' P} xt (M@{X T P'} xt t)) : M@{X T P} xt t :=
    match x with
    | pinr x => x
    | pinl v => pinl v
    end.

  Definition Mfail@{X T P} : forall (x : Type@{X}) (t : Type@{T}) , x -> M@{X T P} x t := @pinl.

  Definition Mor@{X T P} (x : Type@{X}) (t : Type@{T}) (l r : M@{X T P} x t) : M@{X T P} x t :=
    match l with
    | pinl _ => r
    | l => l
    end.

  Definition Mrebuild@{X Y A P} (x : Type@{X}) (y : Type@{Y}) (t : Type@{A})
             (f : x -> y) (c : M@{X A P} x t) : M@{Y A P} y t :=
    match c with
    | pinl x => pinl (f x)
    | pinr y => pinr y
    end.

  Definition Mok@{X T P} {X : Type@{X}} {T : Type@{T}}
  (fail : X -> Prop) (succ : T -> Prop) (c : M@{X T P} X T) : Prop :=
    match c with
    | pinl x => fail x
    | pinr x => succ x
    end.

  Theorem Mok_Melim@{X T P Z}
  : forall {X: Type@{X}} {T : Type@{T}} {U : Type@{Z}} (P : _ -> Prop) (Q : _ -> Prop) (R : _ -> Prop) (m : M X T) (succ : T -> U) (default : U),
      Mok P Q m ->
      (forall x, Q x -> R (succ x)) ->
      (forall x, P x -> R default) ->
      R (Melim@{X T P Z} m succ default).
  Proof.
    destruct m; simpl; eauto.
  Defined.

  Theorem Mok_conseq@{X T P}
  : forall {X : Type@{X}} {T : Type@{T}} (P P' : X -> Prop) (Q Q' : T -> Prop) (c : M@{X T P} X T),
      Mok P Q c ->
      (forall x : X, P x -> P' x) ->
      (forall x : T, Q x -> Q' x) ->
      Mok@{X T P} P' Q' c.
  Proof.
    destruct c; simpl; auto.
  Defined.

  Theorem Mok_Mmap : forall x t u (f : t -> u) P Q (c : M x t),
      Mok P Q c ->
      Mok P (fun x => pexists y, peq x (f y) /\ Q y) (Mmap f c).
  Proof.
    destruct c; simpl; eauto. eexists. split; eauto. constructor.
  Defined.

  Theorem Mok_Mret@{X T P} : forall {x : Type@{X}} {t : Type@{T}} (c : t),
      Mok@{X T P} (fun _ => False) (fun x => peq x c) (@Mret@{X T P} x t c).
  Proof.
    compute. auto. constructor.
  Defined.

  Theorem Mok_Mbind@{X T U P}
  : forall {x : Type@{X}} {t : Type@{T}} {u : Type@{U}}
      (P : x -> Prop) (Q : t -> Prop) (P' : t -> x -> Prop) (Q' : t -> u -> Prop) (c : M x t) (k : t -> M x u),
      Mok@{X T P} P Q c ->
      (forall x : t, Mok@{X U P} (P' x) (Q' x) (k x)) ->
      Mok@{X U P}
         (fun x => P x \/ pexists y, Q y /\ P' y x)
         (fun x => pexists y, Q y /\ Q' y x)
         (Mbind@{X T U P} c k).
  Proof.
    destruct c; simpl; eauto.
    intros. specialize (H0 t0). destruct (k t0); simpl; eauto.
    simpl in *. right; eexists; eauto. simpl in *. eexists; eauto.
  Defined.

  Theorem Mok_Mjoin@{X T P P'}
  : forall (x : Type@{X}) (t : Type@{T}) P P' Q Q' (c : M@{X P' P} x (M@{X T P'} x t)),
      Mok@{X P' P} P Q c ->
      (forall m, Q m -> Mok@{X T P'} P' Q' m) ->
      Mok (fun x => P x \/ P' x) Q' (Mjoin@{X T P P'} c).
  Proof. destruct c. simpl; auto.
         simpl. intros.
         apply H0 in H; clear - H.
         destruct m; simpl in *; auto.
  Defined.

  Theorem Mok_Mfail@{X T P} : forall (x : Type@{X}) (t : Type@{T}) (v : x),
    Mok (fun x => peq x v) (fun _ => False) (@Mfail@{X T P} x t v).
  Proof. compute. auto. constructor. Defined.

  Theorem Mok_Mor@{X T P} : forall (x : Type@{X}) (t : Type@{T})
      (l r : M@{X T P} x t) (P : x -> Prop) (Q Q' : t -> Prop),
    Mok P Q l ->
    Mok P Q' r ->
    Mok P (fun x => Q x \/ Q' x) (Mor l r).
  Proof. destruct l; auto.
         - destruct r; eauto; simpl; tauto.
         - simpl. tauto.
  Defined.

  Theorem Mok_Mrebuild@{X Y A P}
  : forall (x : Type@{X}) (y : Type@{Y}) (t : Type@{A})
      (f : x -> y) (c : M@{X A P} x t) P Q,
      Mok P Q c ->
      Mok (fun x => pexists y, peq x (f y) /\ P y) Q (Mrebuild f c).
  Proof. destruct c; simpl; eauto. eexists. split; eauto. constructor. Defined.

End PtrnEither.
