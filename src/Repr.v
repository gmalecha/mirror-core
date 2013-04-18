Require Import List.
Require Import Omega.
Require Compare_dec.

Set Implicit Arguments.
Set Strict Implicit.

(** This is an alternative representation 
 ** 1) it avoids nats (including comparison)
 ** 2) it is canonical
 ** 3) it optimizes the common case of prefixes
 **)
Section Repr.
  Section parametric.
    Variable T : Type.
    Record Repr : Type :=
    { footprint : list (option T)
    ; default : T 
    }.

    Definition nil_Repr (d : T) : Repr :=
      {| footprint := nil
       ; default := d
      |}.

    Definition listToRepr (ls : list T) (d : T) : Repr :=
      {| footprint := map (@Some _) ls
       ; default := d
      |}.

    Definition listOptToRepr (ls : list (option T)) (d : T) : Repr :=
      {| footprint := ls
       ; default := d
      |}.

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

    Definition repr_combine (l r : Repr) : Repr :=
      Eval cbv delta [ join ] in 
        match l , r with
          | {| footprint := lf ; default := ld |} ,
            {| footprint := rf ; default := rd |} =>
            {| footprint := join lf rf ; default := ld |}
        end.

    Lemma repr_idempotent : forall a b,
      repr a (repr a b) = repr a b.
    Proof.
      clear. destruct a.
      simpl. induction footprint0; simpl; intros; auto.
      destruct a; simpl; auto. f_equal. rewrite IHfootprint0. auto.
      destruct b; auto. rewrite IHfootprint0; auto. simpl.
      rewrite IHfootprint0. auto.
    Qed.

  End parametric.
End Repr.

Ltac reduce_repr_list ls :=
  eval cbv beta zeta delta [ 
    repr_combine repr listOptToRepr listToRepr nil_Repr
    map 
  ] in ls.
