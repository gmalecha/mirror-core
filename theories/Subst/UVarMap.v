Require Import Coq.PArith.BinPos.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.FSets.FMapInterface.
Require Import MirrorCore.ExprI.

Set Implicit Arguments.
Set Strict Implicit.

Let uvar : Type := nat.

Module UVar_ord <: OrderedType.OrderedType with Definition t := uvar
                                           with Definition eq := @eq uvar.
  Definition t := uvar.
  Definition eq := @eq uvar.
  Definition lt := @lt.

  Theorem eq_refl : forall x, eq x x.
  Proof. reflexivity. Qed.

  Theorem eq_sym : forall a b, eq a b -> eq b a.
  Proof. intros; symmetry; auto. Qed.

  Theorem eq_trans : forall a b c, eq a b -> eq b c -> eq a c.
  Proof. intros; etransitivity; eauto. Qed.

  Theorem lt_trans : forall a b c, lt a b -> lt b c -> lt a c.
  Proof. eapply Lt.lt_trans. Qed.

  Theorem lt_not_eq : forall a b, lt a b -> ~(eq a b).
  Proof. eapply NPeano.Nat.lt_neq. Qed.

  Definition compare (x y : t) : OrderedType.Compare lt eq x y :=
    match Compare_dec.nat_compare x y as r return
      Compare_dec.nat_compare x y = r -> OrderedType.Compare lt eq x y
      with
      | Lt => fun pf => OrderedType.LT (lt:=lt) (Compare_dec.nat_compare_Lt_lt _ _ pf)
      | Eq => fun pf => OrderedType.EQ (lt:=lt) (Compare_dec.nat_compare_eq _ _ pf)
      | Gt => fun pf => OrderedType.GT (lt:=lt) (Compare_dec.nat_compare_Gt_gt _ _ pf)
    end (refl_equal _).

  Definition eq_dec (x y : nat) : {x = y} + {x <> y} :=
    match EqNat.beq_nat x y as r return
      EqNat.beq_nat x y = r -> {x = y} + {x <> y} with
      | true => fun pf => left (EqNat.beq_nat_true _ _ pf)
      | false => fun pf => right (EqNat.beq_nat_false _ _ pf)
    end (refl_equal _).
End UVar_ord.

Module MAP <: WS with Definition E.t := uvar
                 with Definition E.eq := @eq uvar.
  Module E := UVar_ord.

  Definition to_key : uvar -> positive :=
    Pos.of_succ_nat.

  Definition from_key : positive -> uvar :=
    fun p => pred (Pos.to_nat p).

  Definition key := uvar.
  Hint Transparent key.

  Definition t : Type -> Type := PositiveMap.t.
  (** the abstract type of maps *)

  Section Types.

    Variable elt:Type.

    Definition empty : t elt :=
      Eval red in PositiveMap.empty _.
    (** The empty map. *)

    Definition is_empty : t elt -> bool :=
      Eval red in @PositiveMap.is_empty _.
    (** Test whether a map is empty or not. *)

    Definition add (k : key) : elt -> t elt -> t elt :=
      Eval red in PositiveMap.add (to_key k).
    (** [add x y m] returns a map containing the same bindings as [m],
	plus a binding of [x] to [y]. If [x] was already bound in [m],
	its previous binding disappears. *)

    Definition find (k : key) : t elt -> option elt :=
      Eval red in PositiveMap.find (to_key k).
    (** [find x m] returns the current binding of [x] in [m],
	or [None] if no such binding exists. *)

    Definition remove (k : key) : t elt -> t elt :=
      Eval red in PositiveMap.remove (to_key k).
    (** [remove x m] returns a map containing the same bindings as [m],
	except for [x] which is unbound in the returned map. *)

    Definition mem (k : key) : t elt -> bool :=
      Eval red in PositiveMap.mem (to_key k).
    (** [mem x m] returns [true] if [m] contains a binding for [x],
	and [false] otherwise. *)

    Variable elt' elt'' : Type.

    Definition map : (elt -> elt') -> t elt -> t elt' :=
      Eval red in @PositiveMap.map _ _.
    (** [map f m] returns a map with same domain as [m], where the associated
	value a of all bindings of [m] has been replaced by the result of the
	application of [f] to [a]. Since Coq is purely functional, the order
        in which the bindings are passed to [f] is irrelevant. *)

    Definition mapi (f : key -> elt -> elt') : t elt -> t elt' :=
      Eval red in @PositiveMap.mapi _ _ (fun k v => f (from_key k) v).
    (** Same as [map], but the function receives as arguments both the
	key and the associated value for each binding of the map. *)

    Definition map2 :
     (option elt -> option elt' -> option elt'') -> t elt -> t elt' ->  t elt'' :=
      Eval red in @PositiveMap.map2 _ _ _.
    (** [map2 f m m'] creates a new map whose bindings belong to the ones
        of either [m] or [m']. The presence and value for a key [k] is
        determined by [f e e'] where [e] and [e'] are the (optional) bindings
        of [k] in [m] and [m']. *)

    Definition elements (m : t elt) : list (key*elt) :=
      Eval red in List.map (fun kv => let '(k,v) := kv in
                                      (from_key k, v)) (PositiveMap.elements m).
    (** [elements m] returns an assoc list corresponding to the bindings
        of [m], in any order. *)

    Definition cardinal : t elt -> nat :=
      Eval red in @PositiveMap.cardinal _.
    (** [cardinal m] returns the number of bindings in [m]. *)

    Definition fold (A: Type) (f : key -> elt -> A -> A) : t elt -> A -> A :=
      Eval red in @PositiveMap.fold _ A (fun k => f (from_key k)).
      
    (** [fold f m a] computes [(f kN dN ... (f k1 d1 a)...)],
	where [k1] ... [kN] are the keys of all bindings in [m]
	(in any order), and [d1] ... [dN] are the associated data. *)

    Definition equal : (elt -> elt -> bool) -> t elt -> t elt -> bool :=
      Eval red in @PositiveMap.equal _.
    (** [equal cmp m1 m2] tests whether the maps [m1] and [m2] are equal,
      that is, contain equal keys and associate them with equal data.
      [cmp] is the equality predicate used to compare the data associated
      with the keys. *)

    Section Spec.

      Variable m m' m'' : t elt.
      Variable x y z : key.
      Variable e e' : elt.

      Definition MapsTo (k : key) : elt -> t elt -> Prop :=
        PositiveMap.MapsTo (to_key k).

      Definition In (k:key)(m: t elt) : Prop := exists e:elt, MapsTo k e m.

      Definition Empty m := forall (a : key)(e:elt) , ~ MapsTo a e m.

      Definition eq_key (p p':key*elt) := E.eq (fst p) (fst p').

      Definition eq_key_elt (p p':key*elt) :=
          E.eq (fst p) (fst p') /\ (snd p) = (snd p').

    (** Specification of [MapsTo] *)
      Theorem MapsTo_1 : E.eq x y -> MapsTo x e m -> MapsTo y e m.
      Admitted.

    (** Specification of [mem] *)
      Theorem mem_1 : In x m -> mem x m = true.
      Admitted.
      Theorem mem_2 : mem x m = true -> In x m.
      Admitted.

    (** Specification of [empty] *)
      Theorem empty_1 : Empty empty.
      Admitted.

    (** Specification of [is_empty] *)
      Theorem is_empty_1 : Empty m -> is_empty m = true.
      Admitted.
      Theorem is_empty_2 : is_empty m = true -> Empty m.
      Admitted.

    (** Specification of [add] *)
      Theorem add_1 : E.eq x y -> MapsTo y e (add x e m).
      Admitted.
      Theorem add_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
      Admitted.
      Theorem add_3 : ~ E.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
      Admitted.

    (** Specification of [remove] *)
      Theorem remove_1 : E.eq x y -> ~ In y (remove x m).
      Admitted.
      Theorem remove_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
      Admitted.
      Theorem remove_3 : MapsTo y e (remove x m) -> MapsTo y e m.
      Admitted.

    (** Specification of [find] *)
      Theorem find_1 : MapsTo x e m -> find x m = Some e.
      Admitted.
      Theorem find_2 : find x m = Some e -> MapsTo x e m.
      Admitted.

    (** Specification of [elements] *)
      Theorem elements_1 :
        MapsTo x e m -> InA eq_key_elt (x,e) (elements m).
      Admitted.
      Theorem elements_2 :
        InA eq_key_elt (x,e) (elements m) -> MapsTo x e m.
      Admitted.
      (** When compared with ordered maps, here comes the only
         property that is really weaker: *)
      Theorem elements_3w : NoDupA eq_key (elements m).
      Admitted.

    (** Specification of [cardinal] *)
      Theorem cardinal_1 : cardinal m = length (elements m).
      Admitted.

    (** Specification of [fold] *)
      Theorem fold_1 :
	forall (A : Type) (i : A) (f : key -> elt -> A -> A),
        fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
      Admitted.

    (** Equality of maps *)

    (** Caveat: there are at least three distinct equality predicates on maps.
      - The simpliest (and maybe most natural) way is to consider keys up to
        their equivalence [E.eq], but elements up to Leibniz equality, in
        the spirit of [eq_key_elt] above. This leads to predicate [Equal].
      - Unfortunately, this [Equal] predicate can't be used to describe
        the [equal] function, since this function (for compatibility with
        ocaml) expects a boolean comparison [cmp] that may identify more
        elements than Leibniz. So logical specification of [equal] is done
        via another predicate [Equivb]
      - This predicate [Equivb] is quite ad-hoc with its boolean [cmp],
        it can be generalized in a [Equiv] expecting a more general
        (possibly non-decidable) equality predicate on elements *)

     Definition Equal m m' := forall y, find y m = find y m'.
     Definition Equiv (eq_elt:elt->elt->Prop) m m' :=
         (forall k, In k m <-> In k m') /\
         (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
     Definition Equivb (cmp: elt->elt->bool) := Equiv (Cmp cmp).

     (** Specification of [equal] *)

     Variable cmp : elt -> elt -> bool.

     Theorem equal_1 : Equivb cmp m m' -> equal cmp m m' = true.
     Admitted.
     Theorem equal_2 : equal cmp m m' = true -> Equivb cmp m m'.
     Admitted.

    End Spec.
   End Types.

    (** Specification of [map] *)
      Parameter map_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)(f:elt->elt'),
        MapsTo x e m -> MapsTo x (f e) (map f m).
      Parameter map_2 : forall (elt elt':Type)(m: t elt)(x:key)(f:elt->elt'),
        In x (map f m) -> In x m.

    (** Specification of [mapi] *)
      Parameter mapi_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)
        (f:key->elt->elt'), MapsTo x e m ->
        exists y, E.eq y x /\ MapsTo x (f y e) (mapi f m).
      Parameter mapi_2 : forall (elt elt':Type)(m: t elt)(x:key)
        (f:key->elt->elt'), In x (mapi f m) -> In x m.

    (** Specification of [map2] *)
      Parameter map2_1 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
	(x:key)(f:option elt->option elt'->option elt''),
	In x m \/ In x m' ->
        find x (map2 f m m') = f (find x m) (find x m').

     Parameter map2_2 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
	(x:key)(f:option elt->option elt'->option elt''),
        In x (map2 f m m') -> In x m \/ In x m'.
End MAP.

Require Coq.FSets.FMapAVL.

Module MAP2 := FMapAVL.Make UVar_ord.