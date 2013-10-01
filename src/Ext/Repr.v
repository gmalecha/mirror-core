Set Implicit Arguments.
Set Strict Implicit.

Module Type ReprType.
  Parameter Key : Type.
  Parameter Env : Type -> Type.
  Parameter Repr : Type -> Type.

  Parameter Env_get : forall T, Env T -> Key -> option T.

  Parameter Repr_nil : forall T, T -> Repr T.

  Parameter Repr_join : forall T, Repr T -> Repr T -> Repr T.

  Parameter repr : forall T, Repr T -> Env T -> Env T.

  (** These are never used but are useful for sanity checking.
   ** To enjoy nice computational properties, they must be
   ** provable without destructing the [Env] value.
   **)
  Parameter Repr_compat : forall T, Repr T -> Repr T -> Prop.

  Axiom repr_nil : forall T (t : T) x, repr (Repr_nil t) x = x.

  Axiom repr_idempotent : forall T (x : Repr T) e, repr x (repr x e) = repr x e.

  Axiom repr_comm : forall T (x y : Repr T),
    Repr_compat x y ->
    forall e, repr x (repr y e) = repr y (repr x e).

End ReprType.

Module ListRepr <: ReprType with Definition Env := list
                            with Definition Key := nat.
  Require Import List.

  (** This implementation uses lists **)
  Section parametric.
    Variable T : Type.
    Definition Key : Type := nat.
    Definition Env : Type := list T.
    Definition Env_get (e : Env) (k : Key) : option T :=
      nth_error e k.

    Record Repr' : Type :=
    { footprint : list (option T)
    ; default : T
    }.
    Definition Repr := Repr'.

    Definition Repr_nil (d : T) : Repr :=
      {| footprint := nil
       ; default := d
      |}.

(*
    Definition listToRepr (ls : list T) (d : T) : Repr :=
      {| footprint := map (@Some _) ls
       ; default := d
      |}.

    Definition listOptToRepr (ls : list (option T)) (d : T) : Repr :=
      {| footprint := ls
       ; default := d
      |}.
*)

    Fixpoint repr' (d : T) (ls : list (option T)) : list T -> list T :=
      match ls with
        | nil => fun x => x
        | None :: ls => fun x =>
          match x with
            | nil => d
            | a :: _ => a
          end :: repr' d ls (tl x)
        | Some v :: ls => fun x =>
          v :: repr' d ls (tl x)
      end.

    Definition repr (l : Repr) : list T -> list T :=
      Eval cbv delta [ repr' ] in
        match l with
          | {| footprint := f ; default := d |} =>
            repr' d f
        end.

    Fixpoint join (ls rs : list (option T)) : list (option T) :=
      match ls , rs with
        | nil , rs => rs
        | ls , nil => ls
        | l :: ls , r :: rs =>
          match l with
            | Some _ => l
            | None => r
          end :: join ls rs
      end.

    Definition Repr_join (l r : Repr) : Repr :=
      Eval cbv delta [ join ] in
        match l , r with
          | {| footprint := lf ; default := ld |} ,
            {| footprint := rf ; default := rd |} =>
            {| footprint := join lf rf ; default := ld |}
        end.

    Inductive compat_opt : option T -> option T -> Prop :=
    | compat_Lnone : forall r, compat_opt None r
    | compat_Rnone : forall l, compat_opt l None
    | compat_some : forall v, compat_opt (Some v) (Some v).

    Inductive compat : list (option T) -> list (option T) -> Prop :=
    | compat_Lnil : forall r, compat nil r
    | compat_Rnil : forall l, compat l nil
    | compat_cons : forall l ls r rs,
      compat_opt l r ->
      compat ls rs ->
      compat (l :: ls) (r :: rs).

    Definition Repr_compat (l r : Repr) : Prop :=
      l.(default) = r.(default) /\
      compat l.(footprint) r.(footprint).

    Theorem repr_nil : forall (t : T) x, repr (Repr_nil t) x = x.
    Proof. reflexivity. Qed.

    Theorem repr_idempotent : forall (x : Repr) e, repr x (repr x e) = repr x e.
    Proof.
      destruct x; simpl.
      induction footprint0; simpl; try reflexivity.
      simpl; destruct a; intros; f_equal; simpl; eapply IHfootprint0.
    Qed.

    Theorem repr_comm : forall (x y : Repr),
      Repr_compat x y ->
      forall e, repr x (repr y e) = repr y (repr x e).
    Proof.
      destruct x; destruct y; simpl.
      unfold Repr_compat; simpl. destruct 1; subst.
      induction H0; auto.
      intros; destruct H.
      { destruct r; simpl; f_equal; eauto. }
      { destruct l; simpl; f_equal; eauto. }
      { f_equal; eauto. }
    Qed.

  End parametric.

  Ltac reduce_repr_list ls := ls.
(*
    eval cbv beta zeta delta [
      repr_combine repr listOptToRepr listToRepr nil_Repr
      map
    ] in ls.
*)

End ListRepr.

Require Import ExtLib.Data.Map.FMapPositive.
Module PMapRepr <: ReprType with Definition Env := pmap
                            with Definition Key := positive.

  (** This implementation uses lists **)
  Section parametric.
    Variable T : Type.
    Definition Key : Type := positive.
    Definition Env : Type := pmap T.
    Definition Env_get (e : Env) (k : Key) : option T :=
      Maps.lookup k e.

    Definition Repr := pmap T.

    Definition Repr_nil (d : T) : Repr :=
      Maps.empty.

(*
    Definition listToRepr (ls : list T) (d : T) : Repr :=
      {| footprint := map (@Some _) ls
       ; default := d
      |}.

    Definition listOptToRepr (ls : list (option T)) (d : T) : Repr :=
      {| footprint := ls
       ; default := d
      |}.
*)
    Fixpoint pmap_lunion (f m : pmap T) : pmap T :=
      match f with
        | Empty => m
        | Branch d l r =>
          Branch (match d with
                    | Some x => Some x
                    | None => pmap_here m
                  end)
                 (pmap_lunion l (pmap_left m)) (pmap_lunion r (pmap_right m))
      end.

    Definition repr : Repr -> Env -> Env :=
      pmap_lunion.

    Definition Repr_join : Repr -> Repr -> Repr :=
      pmap_lunion.

    Inductive compat_opt : option T -> option T -> Prop :=
    | compat_Lnone : forall r, compat_opt None r
    | compat_Rnone : forall l, compat_opt l None
    | compat_some : forall v, compat_opt (Some v) (Some v).

    Inductive compat : pmap T -> pmap T -> Prop :=
    | compat_Lnil : forall r, compat (Empty _) r
    | compat_Rnil : forall l, compat l (Empty _)
    | compat_cons : forall l ls ls' r rs rs',
      compat_opt l r ->
      compat ls rs ->
      compat ls' rs' ->
      compat (Branch l ls ls') (Branch r rs rs').

    Definition Repr_compat : Repr -> Repr -> Prop := compat.

    Theorem repr_nil : forall (t : T) x, repr (Repr_nil t) x = x.
    Proof. reflexivity. Qed.

    Theorem repr_idempotent : forall (x : Repr) e, repr x (repr x e) = repr x e.
    Proof.
      unfold repr.
      induction x; simpl; intros; try reflexivity.
      f_equal; eauto.
      destruct o; auto.
    Qed.

    Theorem repr_comm : forall (x y : Repr),
      Repr_compat x y ->
      forall e, repr x (repr y e) = repr y (repr x e).
    Proof.
      induction 1; simpl; intros; auto.
      f_equal; eauto. destruct l; destruct r; auto.
      inversion H; auto.
    Qed.

  End parametric.
End PMapRepr.
