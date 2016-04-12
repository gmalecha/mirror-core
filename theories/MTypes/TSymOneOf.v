Require Import ExtLib.Data.Positive.
Require Import ExtLib.Data.PList.
Require Import ExtLib.Data.Eq.UIP_trans.
Require Import ExtLib.Tactics.

Require Import MirrorCore.MTypes.ModularTypes.
Require Import MirrorCore.TypesI.

Set Implicit Arguments.
Set Strict Implicit.
Set Printing Universes.

(** TODO(gmalecha): This should use the maps in FMapPositive from ExtLib.
 **)
Module OneOfType.

  Definition TypeR := Type.
  Definition TypeS := Type.

  Inductive _option : TypeS :=
  | _Some : (nat -> TypeR) -> _option
  | _None.
  Arguments _None.
  Arguments _Some _.

  Inductive pmap : TypeS :=
  | Empty : pmap
  | Branch : _option -> pmap -> pmap -> pmap.
  Arguments Empty.
  Arguments Branch _ _ _.

  Definition pmap_here (p : pmap) : _option :=
    match p with
    | Empty => _None
    | Branch d _ _ => d
    end.
  Definition pmap_left (p : pmap) : pmap :=
    match p with
    | Empty => Empty
    | Branch _ l _ => l
    end.
  Definition pmap_right (p : pmap) : pmap :=
    match p with
    | Empty => Empty
    | Branch _ _ r => r
    end.

  Fixpoint pmap_lookup' (ts : pmap) (p : positive) : _option :=
    match p with
    | xH => pmap_here ts
    | xI p => pmap_lookup' (pmap_right ts) p
    | xO p => pmap_lookup' (pmap_left ts) p
    end.

  Fixpoint pmap_insert (p : positive) (ts : pmap) (x : nat -> TypeR) : pmap :=
    match p with
    | xH => Branch (_Some x) (pmap_left ts) (pmap_right ts)
    | xO p => Branch (pmap_here ts)
                     (pmap_insert p (pmap_left ts) x)
                     (pmap_right ts)
    | xI p => Branch (pmap_here ts)
                     (pmap_left ts)
                     (pmap_insert p (pmap_right ts) x)
    end.

  Set Primitive Projections.

  Definition type_nth (p : pmap) (k : positive) (n : nat) : TypeR :=
    match pmap_lookup' p k return TypeR with
    | _None => Empty_set
    | _Some T => T n
    end.

  Record OneOf (ts : pmap) (x : nat) : Type := mkOneOf
  { index : positive
  ; value : type_nth ts index x
  }.

  Definition Into {ts} {T : nat -> TypeR} x (n : positive)
             (pf : pmap_lookup' ts n = _Some T)
  : T x -> OneOf ts x :=
    match pf in _ = X return match X return TypeR with
                             | _Some T => T x
                             | _None => Empty_set
                             end -> OneOf ts x
    with
    | eq_refl => @mkOneOf ts x n
    end.

  Fixpoint asNth' {ts : pmap} {n} (p p' : positive)
  : match pmap_lookup' ts p' return TypeR with
    | _None => Empty_set
    | _Some T => T n
    end -> option (type_nth ts p n) :=
  match p as p , p' as p'
        return type_nth ts p' n -> option (type_nth ts p n)
  with
    | xH , xH => Some
    | xI p , xI p' => asNth' p p'
    | xO p , xO p' => asNth' p p'
    | _ , _ => fun _ => None
  end.

  Definition asNth {ts : pmap} {n} (p : positive) (oe : OneOf ts n)
  : option (type_nth ts p n) :=
    @asNth' ts n p oe.(index) oe.(value).

  Definition OutOf {ts} {T : nat -> TypeR} {x} (n : positive)
             (pf : pmap_lookup' ts n = _Some T)
  : OneOf ts x -> option (T x) :=
    match pf in _ = X
          return OneOf ts x ->
                 option match X return TypeR with
                        | _None => Empty_set
                        | _Some T => T x
                        end
    with
    | eq_refl => asNth _
    end.

  Global Instance Injective_OneOf n m i1 i2 v1 v2
  : Injective (@eq (OneOf m n)
                   {| index := i1 ; value := v1 |}
                   {| index := i2 ; value := v2 |}) :=
  { result := exists pf : i2 = i1,
      v1 = match pf in _ = T
                 return type_nth m T n
           with
           | eq_refl => v2
           end
  ; injection := fun H =>
      match H in _ = h
            return exists pf : index h = i1 ,
          v1 = match pf in (_ = T)
                     return type_nth m T n
               with
               | eq_refl => value h
               end
      with
      | eq_refl => @ex_intro _ _ eq_refl eq_refl
      end
  }.


  Definition asNth'' {ts : pmap} {n} p (x : OneOf ts n)
  : option (type_nth ts p n) :=
    match Pos.eq_dec (index x) p with
    | left pf' => Some match pf' in _ = X
                             return type_nth ts X n
                       with
                       | eq_refl => value x
                       end
    | right _ => None
    end.

  Theorem asNth'_asNth''
  : forall ts n p x,
      @asNth' ts n p (index x) (value x) = @asNth'' ts n p x.
  Proof using.
    destruct x. unfold asNth''. simpl.
    destruct (Pos.eq_dec index0 p); subst.
    { revert value0; revert ts.
      induction p; simpl; intros; eauto. }
    { revert value0; revert ts; generalize dependent index0.
      induction p; destruct index0; simpl; intros; eauto.
      { assert (index0 <> p) by congruence.
        eauto. }
      { assert (index0 <> p) by congruence.
        eauto. }
      { congruence. } }
  Qed.

  Lemma asNth'_get_lookup
  : forall n p ts v, asNth' (ts:=ts) (n:=n) p p v = Some v.
  Proof.
    induction p; simpl; intros; eauto.
  Qed.

  Require Import MirrorCore.Util.Compat.

  Theorem Outof_Into : forall n ts T p pf v,
    @OutOf ts n T p pf (@Into ts n T p pf v) = Some v.
  Proof using.
    unfold OutOf, Into.
    intros.
    autorewrite_with_eq_rw.
    unfold asNth. simpl.
    rewrite asNth'_get_lookup.
    { generalize dependent (pmap_lookup' ts p).
      intros. subst. reflexivity. }
  Qed.

  Theorem asNth_eq
    : forall ts n p oe v,
      @asNth ts n p oe = Some v ->
      oe = {| index := p ; value := v |}.
  Proof.
    unfold asNth.
    destruct oe; simpl.
    revert value0. revert index0. revert ts.
    induction p; destruct index0; simpl; intros;
    try congruence; eapply IHp in H; inv_all; subst; reflexivity.
  Defined.

  Theorem Into_OutOf : forall ts n T p pf v e,
      @OutOf ts n T p pf e = Some v ->
      @Into ts n T p pf v = e.
  Proof using.
    unfold OutOf, Into.
    intros. revert H.
    autorewrite_with_eq_rw.
    unfold asNth.
    destruct e; simpl in *.
    intro.
    assert (p = index0).
    { destruct (asNth' p index0 value0) eqn:?; try congruence.
      inv_all. subst.
      clear - Heqo.
      revert Heqo.
      revert value0 t.
      revert index0. revert ts.
      induction p; destruct index0; simpl; intros; try congruence.
      { f_equal. eauto. }
      { f_equal. eauto. } }
    subst.
    rewrite asNth'_get_lookup in H. inv_all. subst.
    f_equal. clear.
    unfold type_nth in *.
    destruct pf. reflexivity.
  Qed.

  Universe UPmap.
  Polymorphic Fixpoint list_to_pmap_aux
              (lst : plist@{UPmap} (nat -> TypeR)) (p : positive) : pmap :=
    match lst with
    | pnil => OneOfType.Empty
    | pcons x xs => OneOfType.pmap_insert p (list_to_pmap_aux xs (p + 1)) x
  end.

  Definition list_to_pmap (lst : plist@{UPmap} (nat -> TypeR)) := list_to_pmap_aux lst 1.

End OneOfType.

Import OneOfType.

Section TSym_OneOf.
  Context {typ : nat -> Type} {TS : TSym typ}.

  Definition TSym_Empty_set : TSym (fun _ => Empty_set) :=
  {| symbolD := fun n (x : Empty_set) => match x with end
   ; symbol_dec := fun _ x _ => match x with end
   |}.

  Instance TSymOneOf (m : pmap)
    (H : forall p, TSym (type_nth m p))
  : TSym (OneOf m) :=
  { symbolD := fun s x => let ts := H x.(index) in
                          @symbolD _ ts _ x.(value)
  ; symbol_dec := fun _ a b =>
    match a as a , b as b return {a = b} + {a <> b} with
    |   {| index := i1 ; value := v1 |}
      , {| index := i2 ; value := v2 |} =>
        match Pos.eq_dec i1 i2 with
        | left pf =>
          match pf in _ = Z return forall x : type_nth _ Z _,
              {mkOneOf m _ i1 v1 = mkOneOf m _ Z x} + {mkOneOf m _ i1 v1 <> mkOneOf m _ Z x} with
          | eq_refl => fun v2 =>
            match @symbol_dec _ (H i1) _ v1 v2 with
            | left pf => left _
            | right _ => right _
            end
          end v2
        | right _ => right _
        end
    end
   }.
  { subst. reflexivity. }
  { intro.
    eapply Injective_OneOf in H0. simpl in H0.
    destruct H0.
    rewrite (uip_trans Pos.eq_dec _ _ x eq_refl) in H0. apply n0. assumption. }
  { intro.
    apply n0.
    change (index ({| index := i1; value := v1 |}) = index {| index := i2; value := v2 |}).
    rewrite H0. reflexivity. }
  Defined.

End TSym_OneOf.
