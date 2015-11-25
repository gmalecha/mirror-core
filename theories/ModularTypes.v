Require Import MirrorCore.TypesI.

Universes Usmall Ularge.

Section parametric.
  Fixpoint type_for_arity (n : nat) : Type@{Ularge} :=
    match n with
    | 0 => Type@{Usmall}
    | S n => Type@{Usmall} -> type_for_arity n
    end.

  Variable symbol : nat -> Type.

  Variable symbolD : forall {n}, symbol n -> type_for_arity n.

  Variable symbol_eq : forall {n} (a b : symbol n), option (a = b).
  Variable symbol_dec : forall {n} (a b : symbol n), {a = b} + {a <> b}.
  Variable symbol_eq_total : forall n a b, @symbol_eq n a b = match @symbol_dec n a b with
                                                              | left x => Some x
                                                              | right _ => None
                                                              end.

  Inductive typn : nat -> Type :=
  | tyArr : typn 0 -> typn 0 -> typn 0
  | tyApp : forall {n}, typn (S n) -> typn 0 -> typn n
  | tyBase : forall n, symbol n -> typn n.

  Fixpoint typnD {n} (t : typn n) : type_for_arity n :=
    match t in typn n return type_for_arity n with
    | tyArr a b => typnD a -> typnD b
    | tyApp a b => (typnD a) (typnD b)
    | tyBase n x => symbolD _ x
    end.

  Fixpoint typn_cast {n : nat} (a : typn n) : forall b : typn n, option (a = b) :=
    match a as a in typn N return forall b : typn N, option (a = b) with
    | tyArr l r => fun b : typn 0 =>
                     match b in typn N return option (match N as N return typn N -> Type with
                                                      | 0 => fun b : typn 0 => tyArr l r = b
                                                      | S x => fun _ => Empty_set
                                                      end b) with
                     | tyArr l' r' =>
                       match typn_cast l l'
                           , typn_cast r r'
                       with
                       | Some pf , Some pf' => Some match pf , pf' with
                                                    | eq_refl , eq_refl => eq_refl
                                                    end
                       | _ , _ => None
                       end
                     | @tyApp _ x y => None
                     | tyBase a z => None
                     end
    | @tyApp n l r => fun b : typn n =>
                        match b in typn N
                              return forall l : typn (S N), (forall b, option (l = b)) -> option (tyApp l r = b)
                        with
                        | @tyApp n' l' r' => fun _ rec =>
                          match rec l' , typn_cast r r' with
                          | Some pf , Some pf' => Some match pf , pf' with
                                                       | eq_refl , eq_refl => eq_refl
                                                       end
                          | _ , _ => None
                          end
                        | _ => fun _ _ => None
                        end l (fun x => typn_cast l x)
    | tyBase n s => fun b : typn n =>
                      match b as b in typn N return forall s : symbol N, option (@tyBase N s = b) with
                      | tyBase n' s' => fun s =>
                                          match symbol_eq _ s s' with
                                          | Some pf => Some match pf with
                                                            | eq_refl => eq_refl
                                                            end
                                          | None => None
                                          end
                      | _ => fun _ => None
                      end s
    end.

  Definition typ_tag {n} (t : typn n) : nat :=
    match t with
    | tyArr _ _ => 0
    | tyApp _ _ => 1
    | tyBase _ _ => 2
    end.
  Lemma tag_inj : forall n (a b : typn n),
      a = b ->
      typ_tag a = typ_tag b.
  Proof using. intros; subst; reflexivity. Qed.

  Fixpoint typn_dec {n : nat} (a : typn n) : forall b : typn n, {a = b} + {not (a = b)}.
  refine
    match a as a in typn N return forall b : typn N, {a = b} + {not (a = b)} with
    | tyArr l r => fun b : typn 0 =>
                     match b in typn N
                           return 0 = N -> {match N as N return typn N -> Prop with
                                   | 0 => fun b : typn 0 => tyArr l r = b
                                   | S x => fun _ => False
                                   end b} + {match N as N return typn N -> Prop with
                                             | 0 => fun b : typn 0 => not (tyArr l r = b)
                                             | S x => fun _ => False
                                             end b} with
                     | tyArr l' r' => fun _ =>
                       match @typn_dec 0 l l'
                           , @typn_dec 0 r r'
                       with
                       | left pf , left pf' => left _
                       | _ , _ => right _
                       end
                     | @tyApp _ x y => fun _ => right _
                     | tyBase a z => fun _ => right _
                     end eq_refl
    | @tyApp n l r => fun b : typn n =>
                        match b in typn N
                              return forall l : typn (S N), (forall b, {l = b} + {not (l = b)}) -> {tyApp l r = b} + {not (tyApp l r = b)}
                        with
                        | @tyApp n' l' r' => fun _ rec =>
                          match rec l' , typn_dec _ r r' with
                          | left pf , left pf' => left _ match pf , pf' with
                                                         | eq_refl , eq_refl => eq_refl
                                                         end
                          | _ , _ => right _
                          end
                        | _ => fun _ _ => right _
                        end l (fun x => typn_dec _ l x)
    | tyBase n s => fun b : typn n =>
                      match b as b in typn N
                            return forall s : symbol N, {@tyBase N s = b} + {not (@tyBase N s = b)}
                      with
                      | tyBase n' s' => fun s =>
                                          match symbol_dec _ s s' with
                                          | left pf => left match pf with
                                                            | eq_refl => eq_refl
                                                            end
                                          | right _ => right _
                                          end
                      | _ => fun _ => right _
                      end s
    end; try solve [ congruence
                   | subst; injection 1; auto
                   | subst; intro; eapply tag_inj in H; simpl in *; congruence
                   ].
  { red. intros. apply n1.
    injection H.
    intros. eapply EqDep.inj_pair2 in H1. auto. }
  { red; intros.
    apply n1. injection H. intros.
    eapply EqDep.inj_pair2 in H0. auto. }
  Defined.

  Inductive typn_acc : forall n, typn n -> forall n', typn n' -> Prop :=
  | tyAcc_tyArrL : forall a b, @typn_acc _ a _ (tyArr a b)
  | tyAcc_tyArrR : forall a b, @typn_acc _ a _ (tyArr b a)
(*  | tyAcc_tyAppL : forall n a b, @typn_acc (S n) b _ (tyApp b a) *)
  | tyAcc_tyAppR : forall n a b, @typn_acc 0 a n (tyApp b a).

  Definition typ0_acc := fun a b : typn 0 => typn_acc 0 a 0 b.

  Theorem wf_typ0_acc : well_founded (fun a b => typn_acc 0 a 0 b).
  Proof using.
    red. intros.
    constructor. revert a.
  Admitted.

  Definition typ := typn 0.

  Instance RType_typ0 : RType typ :=
  { typD := @typnD 0
  ; type_cast := @typn_cast 0
  ; tyAcc := typ0_acc
  }.

  Local Instance EqDec_symbol : forall n, EqDec (symbol n) (@eq (symbol n)).
  Proof.
    red. intros.
    destruct (symbol_dec _ x y); (left + right); assumption.
  Defined.

  Local Instance EqDec_typn : forall n, EqDec (typn n) (@eq (typn n)).
  Proof.
    red. intros.
    eapply typn_dec.
  Defined.

  Theorem typn_cast_refl : forall n a,
      @typn_cast n a a = Some eq_refl.
  Proof.
    induction a; simpl.
    - rewrite IHa1. rewrite IHa2. reflexivity.
    - rewrite IHa1. rewrite IHa2. reflexivity.
    - rewrite symbol_eq_total.
      destruct (symbol_dec n s s); try congruence.
      rewrite (EqDep.UIP_refl e). reflexivity.
  Qed.

  Theorem typn_cast_nrefl : forall x y : typ, typn_cast x y = None -> ~ x = y.
  Proof.
    unfold typ. intros. intro. subst.
    rewrite typn_cast_refl in H. congruence.
  Qed.

  Instance RTypeOk_typ0 : RTypeOk.
  Proof.
    constructor.
    - reflexivity.
    - eapply wf_typ0_acc.
    - destruct pf; reflexivity.
    - destruct pf1; destruct pf2; reflexivity.
    - apply typn_cast_refl.
    - eapply typn_cast_nrefl.
    - eauto with typeclass_instances.
  Qed.
End parametric.