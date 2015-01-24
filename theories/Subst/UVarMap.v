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

  Theorem from_key_to_key : forall x, from_key (to_key x) = x.
    unfold from_key, to_key.
    intros. rewrite Pnat.SuccNat2Pos.id_succ. reflexivity.
  Qed.

  Theorem to_key_from_key : forall x, to_key (from_key x) = x.
    unfold from_key, to_key.
    intros.
    rewrite <- (Pnat.Pos2Nat.id x) at 2.
    assert (Pos.to_nat x <> 0).
    { generalize (Pnat.Pos2Nat.is_pos x). omega. }
    destruct (Pos.to_nat x); try congruence.
    rewrite Pos.of_nat_succ. reflexivity.
  Qed.

  Lemma to_key_inj : forall a b, to_key a = to_key b -> a = b.
  Proof.
    clear. unfold to_key.
    eapply Pnat.SuccNat2Pos.inj_iff.
  Qed.

  Lemma from_key_inj : forall a b, from_key a = from_key b -> a = b.
    unfold from_key. intros.
    destruct (Pnat.Pos2Nat.is_succ a).
    destruct (Pnat.Pos2Nat.is_succ b).
    rewrite H0 in *. rewrite H1 in *. simpl in *.
    subst. rewrite <- H1 in H0.
    eapply Pnat.Pos2Nat.inj_iff in H0. auto.
  Qed.

  Definition key := uvar.
  Hint Transparent key.

  Definition t : Type -> Type := PositiveMap.t.
  (** the abstract type of maps *)

  Section Types.

    Variable elt:Type.

    Definition empty : t elt :=
      PositiveMap.empty _.
    (** The empty map. *)

    Definition is_empty : t elt -> bool :=
      @PositiveMap.is_empty _.
    (** Test whether a map is empty or not. *)

    Definition add (k : key) : elt -> t elt -> t elt :=
      PositiveMap.add (to_key k).
    (** [add x y m] returns a map containing the same bindings as [m],
	plus a binding of [x] to [y]. If [x] was already bound in [m],
	its previous binding disappears. *)

    Definition find (k : key) : t elt -> option elt :=
      PositiveMap.find (to_key k).
    (** [find x m] returns the current binding of [x] in [m],
	or [None] if no such binding exists. *)

    Definition remove (k : key) : t elt -> t elt :=
      PositiveMap.remove (to_key k).
    (** [remove x m] returns a map containing the same bindings as [m],
	except for [x] which is unbound in the returned map. *)

    Definition mem (k : key) : t elt -> bool :=
      PositiveMap.mem (to_key k).
    (** [mem x m] returns [true] if [m] contains a binding for [x],
	and [false] otherwise. *)

    Variable elt' elt'' : Type.

    Definition map : (elt -> elt') -> t elt -> t elt' :=
      @PositiveMap.map _ _.
    (** [map f m] returns a map with same domain as [m], where the associated
	value a of all bindings of [m] has been replaced by the result of the
	application of [f] to [a]. Since Coq is purely functional, the order
        in which the bindings are passed to [f] is irrelevant. *)

    Definition mapi (f : key -> elt -> elt') : t elt -> t elt' :=
      @PositiveMap.mapi _ _ (fun k v => f (from_key k) v).
    (** Same as [map], but the function receives as arguments both the
	key and the associated value for each binding of the map. *)

    Definition map2 :
     (option elt -> option elt' -> option elt'') -> t elt -> t elt' ->  t elt'' :=
      @PositiveMap.map2 _ _ _.
    (** [map2 f m m'] creates a new map whose bindings belong to the ones
        of either [m] or [m']. The presence and value for a key [k] is
        determined by [f e e'] where [e] and [e'] are the (optional) bindings
        of [k] in [m] and [m']. *)

    Definition elements (m : t elt) : list (key*elt) :=
       List.map (fun kv => let '(k,v) := kv in
                           (from_key k, v)) (PositiveMap.elements m).
    (** [elements m] returns an assoc list corresponding to the bindings
        of [m], in any order. *)

    Definition cardinal : t elt -> nat :=
      @PositiveMap.cardinal _.
    (** [cardinal m] returns the number of bindings in [m]. *)

    Definition fold (A: Type) (f : key -> elt -> A -> A) : t elt -> A -> A :=
      @PositiveMap.fold _ A (fun k => f (from_key k)).

    (** [fold f m a] computes [(f kN dN ... (f k1 d1 a)...)],
	where [k1] ... [kN] are the keys of all bindings in [m]
	(in any order), and [d1] ... [dN] are the associated data. *)

    Definition equal : (elt -> elt -> bool) -> t elt -> t elt -> bool :=
      @PositiveMap.equal _.
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
        unfold MapsTo, E.eq; intros. subst.
        eapply PositiveMap.MapsTo_1; eauto. reflexivity.
      Qed.

      (** Specification of [mem] *)
      Theorem mem_1 : In x m -> mem x m = true.
        unfold In, MapsTo, mem.
        intros. change (PositiveMap.mem (to_key x) m = true).
        eapply PositiveMap.mem_1. eapply H.
      Qed.

      Theorem mem_2 : mem x m = true -> In x m.
        unfold mem.
        change (PositiveMap.mem (to_key x) m = true -> In x m).
        eapply PositiveMap.mem_2.
      Qed.

      (** Specification of [empty] *)
      Theorem empty_1 : Empty empty.
        generalize (@PositiveMap.empty_1 elt).
        red. unfold MapsTo, PositiveMap.Empty, PositiveMap.MapsTo.
        eauto.
      Qed.

      (** Specification of [is_empty] *)
      Theorem is_empty_1 : Empty m -> is_empty m = true.
        unfold Empty, is_empty, MapsTo.
        generalize (@PositiveMap.is_empty_1 elt).
        intros. change (PositiveMap.is_empty m = true).
        eapply H. red.
        intros. intro. eapply H0.
        instantiate (2 := from_key a).
        instantiate (1 := e0).
        rewrite to_key_from_key. assumption.
      Qed.
      Theorem is_empty_2 : is_empty m = true -> Empty m.
        unfold is_empty, Empty.
        intros. eapply PositiveMap.is_empty_2 in H.
        red in H. unfold MapsTo. eauto.
      Qed.

      (** Specification of [add] *)
      Theorem add_1 : E.eq x y -> MapsTo y e (add x e m).
        unfold E.eq, MapsTo, add; intros; subst.
        eapply PositiveMap.add_1. reflexivity.
      Qed.
      Theorem add_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
        unfold E.eq, MapsTo, add.
        intros. eapply PositiveMap.add_2; eauto.
        intro. red in H1.
        eapply to_key_inj in H1. auto.
      Qed.
      Theorem add_3 : ~ E.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
        unfold MapsTo, E.eq, add.
        intros. eapply PositiveMap.add_3; eauto.
        unfold PositiveMap.E.eq. intro.
        eapply to_key_inj in H1. auto.
      Qed.

    (** Specification of [remove] *)
      Theorem remove_1 : E.eq x y -> ~ In y (remove x m).
        unfold E.eq, In, remove.
        intros. eapply PositiveMap.remove_1. red.
        subst; reflexivity.
      Qed.
      Theorem remove_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
        unfold E.eq, MapsTo, remove; intros.
        eapply PositiveMap.remove_2; eauto.
        unfold PositiveMap.E.eq. intro.
        eapply to_key_inj in H1. auto.
      Qed.
      Theorem remove_3 : MapsTo y e (remove x m) -> MapsTo y e m.
        unfold remove, MapsTo. intros.
        eapply PositiveMap.remove_3. eauto.
      Qed.

    (** Specification of [find] *)
      Theorem find_1 : MapsTo x e m -> find x m = Some e.
        eapply PositiveMap.find_1.
      Qed.
      Theorem find_2 : find x m = Some e -> MapsTo x e m.
        eapply PositiveMap.find_2.
      Qed.

      (** Specification of [elements] *)
      Theorem elements_1 :
        MapsTo x e m -> InA eq_key_elt (x,e) (elements m).
      Proof.
        unfold MapsTo, eq_key_elt, elements. intros.
        eapply PositiveMap.elements_1 in H.
        induction H.
        { simpl. constructor. simpl.
          destruct H. simpl in *. subst.
          destruct y0; simpl; split; eauto.
          red in H. simpl in *. red.
          subst. rewrite from_key_to_key. reflexivity. }
        { simpl. eapply InA_cons_tl. eauto. }
      Qed.
      Theorem elements_2 :
        InA eq_key_elt (x,e) (elements m) -> MapsTo x e m.
        intros. eapply PositiveMap.elements_2.
        unfold elements in H.
        revert H. clear. revert x. revert e.
        induction (PositiveMap.elements m).
        { simpl. inversion 1. }
        { intros. simpl in H. inversion H; eauto.
          { subst. left. destruct a; simpl in *.
            red in H1. intuition. unfold E.eq in *. simpl in *; subst.
            rewrite to_key_from_key. reflexivity. } }
      Qed.
      (** When compared with ordered maps, here comes the only
         property that is really weaker: *)
      Theorem elements_3w : NoDupA eq_key (elements m).
        unfold elements.
        generalize (PositiveMap.elements_3w m).
        induction 1. constructor.
        simpl. constructor; eauto.
        intro. eapply H.
        clear - H1. destruct x0; simpl in *.
        induction l; inversion H1; clear H1; subst.
        { left. destruct a. red in H0. red in H0. simpl in *.
          red. red. simpl.
          eapply from_key_inj in H0. auto. }
        { right. auto. }
      Qed.

      (** Specification of [cardinal] *)
      Theorem cardinal_1 : cardinal m = length (elements m).
        unfold elements. rewrite map_length.
        eapply PositiveMap.cardinal_1.
      Qed.

      Lemma fold_left_map : forall {T U V : Type}
                                   (f : T -> U) (g : V -> U -> V) ls a,
          fold_left g (List.map f ls) a =
          fold_left (fun a b => g a (f b)) ls a.
      Proof.
        clear. induction ls; simpl; intros; auto.
      Qed.


      (** Specification of [fold] *)
      Theorem fold_1 :
	forall (A : Type) (i : A) (f : key -> elt -> A -> A),
        fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
        unfold fold, elements.
        intros. rewrite fold_left_map.
        rewrite PositiveMap.fold_1.
        revert i.
        induction (PositiveMap.elements m); simpl; auto; intros.
        rewrite IHl. f_equal. destruct a. reflexivity.
      Qed.

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
       unfold Equivb, equal, Equiv.
       intros. eapply PositiveMap.equal_1.
       red. red. split.
       { intros. destruct H. specialize (H (from_key k)).
         clear - H. unfold In, PositiveMap.In, MapsTo in *.
         rewrite to_key_from_key in *. assumption. }
       { intros. destruct H. specialize (@H2 (from_key k) e0 e'0).
         unfold MapsTo in *. rewrite to_key_from_key in *.
         eauto. }
     Qed.
     Theorem equal_2 : equal cmp m m' = true -> Equivb cmp m m'.
       unfold Equivb, equal, Equiv. intros.
       eapply PositiveMap.equal_2  in H.
       red in H. red in H.
       unfold In, MapsTo. split.
       { destruct H. intros. eapply H. }
       { destruct H. intros. eapply H0; eauto. }
     Qed.

    End Spec.
   End Types.

  (** Specification of [map] *)
  Theorem map_1
  : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)(f:elt->elt'),
      MapsTo x e m -> MapsTo x (f e) (map f m).
  Proof.
    unfold MapsTo,map. intros; eapply PositiveMap.map_1; eauto.
  Qed.
  Theorem map_2
  : forall (elt elt':Type)(m: t elt)(x:key)(f:elt->elt'),
      In x (map f m) -> In x m.
  Proof.
    unfold In, MapsTo, map; intros;
    eapply PositiveMap.map_2; eauto.
  Qed.

  (** Specification of [mapi] *)
  Theorem mapi_1
  : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)
           (f:key->elt->elt'), MapsTo x e m ->
                               exists y, E.eq y x /\ MapsTo x (f y e) (mapi f m).
  Proof.
    intros. eapply PositiveMap.mapi_1 with (f := fun a b => f (from_key a) b) in H.
    destruct H as [ y ? ]; exists (from_key y).
    unfold E.eq, MapsTo. destruct H.
    unfold PositiveMap.E.eq in *. subst.
    rewrite from_key_to_key in *. eauto.
  Qed.
  Theorem mapi_2
  : forall (elt elt':Type)(m: t elt)(x:key)
           (f:key->elt->elt'), In x (mapi f m) -> In x m.
  Proof.
    unfold In, mapi, MapsTo; intros.
    eapply PositiveMap.mapi_2. eassumption.
  Qed.

  (** Specification of [map2] *)
  Theorem map2_1
  : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
	   (x:key)(f:option elt->option elt'->option elt''),
      In x m \/ In x m' ->
      find x (map2 f m m') = f (find x m) (find x m').
  Proof.
    intros; eapply PositiveMap.map2_1; eauto.
  Qed.

  Theorem map2_2
  : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
	   (x:key)(f:option elt->option elt'->option elt''),
      In x (map2 f m m') -> In x m \/ In x m'.
  Proof.
    intros. eapply PositiveMap.map2_2. eauto.
  Qed.
End MAP.

Require Coq.FSets.FMapAVL.

Module MAP2 := FMapAVL.Make UVar_ord.