Require Import ExtLib.Tactics.EqDep.
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
  Variable symbol_eq_total : forall n a b,
      @symbol_eq n a b = match @symbol_dec n a b with
                         | left x => Some x
                         | right _ => None
                         end.

  Arguments symbolD {_} _.
  Arguments symbol_dec {_} _ _.
  Arguments symbol_eq {_} _ _.

  Inductive typn : nat -> Type :=
  | tyArr : typn 0 -> typn 0 -> typn 0
  | tyApp : forall {n}, typn (S n) -> typn 0 -> typn n
  | tyBase : forall {n}, symbol n -> typn n.

  Fixpoint typnD {n} (t : typn n) : type_for_arity n :=
    match t in typn n return type_for_arity n with
    | tyArr a b => typnD a -> typnD b
    | tyApp a b => (typnD a) (typnD b)
    | tyBase x => symbolD x
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
      | tyBase z => None
      end
    | @tyApp n l r => fun b : typn n =>
      match b in typn N
            return forall l : typn (S N),
          (forall b, option (l = b)) -> option (tyApp l r = b)
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
    | @tyBase n s => fun b : typn n =>
      match b as b in typn N
            return forall s : symbol N, option (@tyBase N s = b)
      with
      | @tyBase n' s' => fun s =>
                           match symbol_eq s s' with
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
    | tyBase _ => 2
    end.
  Lemma tag_inj : forall n (a b : typn n),
      a = b ->
      typ_tag a = typ_tag b.
  Proof using. intros; subst; reflexivity. Qed.

  Fixpoint typn_dec {n : nat} (a : typn n)
  : forall b : typn n, {a = b} + {not (a = b)}.
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
      | @tyBase a z => fun _ => right _
      end eq_refl
    | @tyApp n l r => fun b : typn n =>
      match b in typn N
            return forall l : typn (S N),
          (forall b, {l = b} + {not (l = b)}) ->
          {tyApp l r = b} + {not (tyApp l r = b)}
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
    | @tyBase n s => fun b : typn n =>
      match b as b in typn N
            return forall s : symbol N,
          {@tyBase N s = b} + {not (@tyBase N s = b)}
      with
      | @tyBase n' s' => fun s =>
                           match symbol_dec s s' with
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

  Inductive typn_acc (a : typn 0) : forall {n}, typn n -> Prop :=
  | tyAcc_tyArrL : forall b, typn_acc a (tyArr a b)
  | tyAcc_tyArrR : forall b, typn_acc a (tyArr b a)
  | tyAcc_tyAppL : forall n b, @typn_acc a (S n) b -> typn_acc a (tyApp b a)
  | tyAcc_tyAppR : forall n b, @typn_acc a n (tyApp b a).

  Theorem wf_typn_acc : forall n (a : typn n), match n with
                                   | 0 => Acc (fun a b => typn_acc a b)
                                   | S n => fun _ => True
                                   end a.
  Proof using.
    induction a.
    - constructor. inversion 1; subst; eauto.
    - destruct n. constructor. inversion 1; subst; eauto.
      trivial.
    - destruct n; auto.
      constructor. inversion 1.
  Defined.

  Definition typ0_acc := fun a b : typn 0 => typn_acc a b.

  Theorem wf_typ0_acc : well_founded typ0_acc.
  Proof using.
    red. eapply wf_typn_acc.
  Defined.

  Definition typ := typn 0.

  Instance RType_typ0 : RType typ :=
  { typD := @typnD 0
  ; type_cast := @typn_cast 0
  ; tyAcc := typ0_acc }.

  Local Instance EqDec_symbol : forall n, EqDec (symbol n) (@eq (symbol n)).
  Proof.
    red. intros.
    destruct (symbol_dec x y); (left + right); assumption.
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
      destruct (symbol_dec s s); try congruence.
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

  Instance Typ0_sym (s : symbol 0) : Typ0 _ (symbolD s) :=
  { typ0 := tyBase s
  ; typ0_cast := eq_refl
  ; typ0_match := fun T (t : typn 0) tr =>
                    match t as t' in typn n
                          return T (match n as n return typn n -> Type with
                                    | 0 => @typD typ (RType_typ0)
                                    | S n => fun _ => typD t
                                    end t') ->
                                 T (match n as n return typn n -> Type with
                                    | 0 => @typD typ (RType_typ0)
                                    | S n => fun _ => typD t
                                    end t')
                    with
                    | @tyBase 0 s' =>
                      match symbol_dec s s' with
                      | left pf => fun _ => match pf with
                                            | eq_refl => tr
                                            end
                      | right _ => fun fa => fa
                      end
                    | _ => fun fa => fa
                    end }.
  Instance Typ0Ok_sym (s : symbol 0) : Typ0Ok (Typ0_sym s).
  Proof using.
    constructor.
    { simpl. intros.
      destruct (symbol_dec s s) eqn:?; try reflexivity.
      - uip_all. reflexivity.
      - exfalso; clear - n. congruence. }
    { intro. refine
        match x as x in typn n
              return match n as n return typn n -> Prop with
                     | 0 => fun x =>
                              (exists pf : Rty x (typ0 (F:=symbolD s)),
                                  forall (T : Type -> Type) (tr : T (symbolD s)) (fa : T (typD x)),
                                    typ0_match T x tr fa =
                                    Relim T pf
                                          match eq_sym (typ0_cast (F:=symbolD s)) in (_ = t) return (T t) with
                                          | eq_refl => tr
                                          end) \/
                              (forall (T : Type -> Type) (tr : T (symbolD s)) (fa : T (typD x)),
                                  typ0_match T x tr fa = fa)
                     | _ => fun _ => True
                     end x
        with
        | tyBase _ => _
        | _ => _
        end; try solve [ right; eauto ].
      { destruct n; auto. }
      { destruct n; auto. simpl.
        destruct (symbol_dec s s0); try solve [ right; eauto ].
        subst. left. exists eq_refl. reflexivity. } }
    { destruct pf. reflexivity. }
  Qed.

  Instance Typ1_sym (s : symbol 1) : Typ1 _ (symbolD s) :=
  { typ1 := fun x => tyApp (tyBase s) x
  ; typ1_cast := fun _ => eq_refl
  ; typ1_match := fun T (t : typn 0) tr =>
      match t as t' in typn n
            return T (match n as n return typn n -> Type with
                      | 0 => @typD typ (RType_typ0)
                      | S n => fun _ => typD t
                      end t') ->
                   T (match n as n return typn n -> Type with
                      | 0 => @typD typ (RType_typ0)
                      | S n => fun _ => typD t
                      end t')
      with
      | @tyApp n _t' x =>
        match n as n
              return forall t' : typn (S n),
            T (match n as n1 return (typn n1 -> Type) with
               | 0 => @typD typ RType_typ0
               | S n1 =>
                 fun _ : typn (S n1) =>
                   @typD (typn 0) RType_typ0 t
               end (@tyApp n t' x)) ->
            T (match n as n1 return (typn n1 -> Type) with
               | 0 => @typD typ RType_typ0
               | S n1 =>
                 fun _ : typn (S n1) =>
                   @typD (typn 0) RType_typ0 t
               end (@tyApp n t' x))
        with
        | 0 => fun t' =>
                 match t' as t' in typn n'
                       return T (match n' as n' return typn n' -> Type with
                                 | 0 => fun _ => unit
                                 | S n' =>
                                   match n' as n' return typn (S n') -> Type with
                                   | 0 => fun t' : typn 1 =>
                                            (@typD typ RType_typ0 (@tyApp 0 t' x))
                                   | S _ => fun _ => unit
                                   end
                                 end t') ->
                              T (match n' as n' return typn n' -> Type with
                                 | 0 => fun _ => unit
                                 | S n' =>
                                   match n' as n' return typn (S n') -> Type with
                                   | 0 => fun t' : typn 1 =>
                                            (@typD typ RType_typ0 (@tyApp 0 t' x))
                                   | S _ => fun _ => unit
                                   end
                                 end t')
                 with
                 | @tyBase n' s' =>
                   match n' as n'
                         return forall s' : symbol n',
                                T (match n' as n'0 return (typn n'0 -> Type) with
                                   | 0 => fun _ : typn 0 => unit
                                   | S n'0 =>
                                     match n'0 as n'1 return (typn (S n'1) -> Type) with
                                     | 0 => fun t'0 : typn 1 => @typD typ RType_typ0 (@tyApp 0 t'0 x)
                                     | S n0 => fun _ : typn (S (S n0)) => unit
                                     end
                                   end (@tyBase n' s')) ->
                                T (match n' as n'0 return (typn n'0 -> Type) with
                                   | 0 => fun _ : typn 0 => unit
                                   | S n'0 =>
                                     match n'0 as n'1 return (typn (S n'1) -> Type) with
                                     | 0 => fun t'0 : typn 1 => @typD typ RType_typ0 (@tyApp 0 t'0 x)
                                     | S n0 => fun _ : typn (S (S n0)) => unit
                                     end
                                   end (@tyBase n' s'))
                   with
                   | 1 => fun s' =>
                            match symbol_dec s s' with
                            | left pf => match pf with
                                         | eq_refl => fun _ => tr x
                                         end
                            | right _ => fun fa => fa
                            end
                   | _ => fun _ fa => fa
                   end s'
                 | _ => fun fa => fa
                 end
        | _ => fun _ fa => fa
        end _t'
      | _ => fun fa => fa
      end }.

  Instance Typ1Ok_sym (s : symbol 1) : Typ1Ok (Typ1_sym s).
  Proof using.
    constructor.
    { simpl. intros.
      destruct (symbol_dec s s).
      - uip_all. reflexivity.
      - exfalso. clear - n. auto. }
    { intros. constructor 4. }
    { compute. inversion 1. reflexivity. }
    { intros.
      refine
        match x as x in typn n
              return match n as n return typn n -> Prop with
                     | 0 => fun x =>
                              (exists (d : typ) (pf : Rty x (typ1 d)),
                                  forall (T : Type -> Type) (tr : forall a : typ, T (symbolD s (typD a)))
                                         (fa : T (typD x)),
                                    typ1_match T x tr fa =
                                    Relim T pf
                                          match eq_sym (typ1_cast d) in (_ = t) return (T t) with
                                          | eq_refl => tr d
                                          end) \/
                              (forall (T : Type -> Type) (tr : forall a : typ, T (symbolD s (typD a)))
                                      (fa : T (typD x)), typ1_match T x tr fa = fa)
                     | _ => fun _ => True
                     end x
        with
        | tyApp _ _ => _
        | _ => _
        end; try solve [ right; reflexivity
                       | destruct n ; auto ].
      destruct n; auto.
      refine
        match t as t in typn n
              return match n as n return typn n -> Prop with
                     | 0 => fun _ => True
                     | 1 => fun t =>
                              (exists (d : typ) (pf : Rty (tyApp t t0) (typ1 d)),
                                  forall (T : Type -> Type) (tr : forall a : typ, T (symbolD s (typD a)))
                                         (fa : T (typD (tyApp t t0))),
                                    typ1_match T (tyApp t t0) tr fa =
                                    Relim T pf
                                          match eq_sym (typ1_cast d) in (_ = t1) return (T t1) with
                                          | eq_refl => tr d
                                          end) \/
                              (forall (T : Type -> Type) (tr : forall a : typ, T (symbolD s (typD a)))
                                      (fa : T (typD (tyApp t t0))), typ1_match T (tyApp t t0) tr fa = fa)
                     | S (S _) => fun _ => True
                     end t
        with
        | tyBase _ => _
        | _ => _
        end; try solve [ auto | do 2 (destruct n; auto) ].
      destruct n; auto.
      destruct n; auto.
      simpl.
      destruct (symbol_dec s s0); auto.
      left.
      exists t0. subst. exists eq_refl. reflexivity. }
    { destruct pf. reflexivity. }
  Qed.

  Instance Typ2_Fun : Typ2 _ RFun :=
  { typ2 := tyArr
  ; typ2_cast := fun _ _ => eq_refl
  ; typ2_match := fun T (x : typn 0) tr =>
    match x as x in typn n
          return T (match n as n return typn n -> Type with
                    | 0 => fun x => typD x
                    | _ => fun _ => unit
                    end x) ->
                 T (match n as n return typn n -> Type with
                    | 0 => fun x => typD x
                    | _ => fun _ => unit
                    end x)
    with
    | tyArr l r => fun _ => tr l r
    | _ => fun fa => fa
    end }.

  Instance Typ2Ok_Fun : Typ2Ok Typ2_Fun.
  Proof using.
    constructor.
    { reflexivity. }
    { constructor. }
    { constructor. }
    { inversion 1. split; reflexivity. }
    { intro.
      refine
        match x as x in typn 0
              return (exists (d r : typ) (pf : Rty x (typ2 d r)),
                         forall (T : Type -> Type)
                                (tr : forall a b : typ, T (RFun (typD a) (typD b)))
                                (fa : T (typD x)),
                           typ2_match T x tr fa =
                           Relim T pf
                                 match eq_sym (typ2_cast d r) in (_ = t) return (T t) with
                                 | eq_refl => tr d r
                                 end) \/
                     (forall (T : Type -> Type)
                             (tr : forall a b : typ, T (RFun (typD a) (typD b)))
                             (fa : T (typD x)), typ2_match T x tr fa = fa)
        with
        | tyArr l r => _
        | _ => _
        end; try solve [ destruct n; try exact @id; right; auto ].
      left. simpl.
      do 2 eexists. exists eq_refl. reflexivity. }
    { destruct pf. reflexivity. }
  Qed.

End parametric.