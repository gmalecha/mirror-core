Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.

Require Import MirrorCore.SymI.
Require Import MirrorCore.TypesI.

Set Implicit Arguments.
Set Strict Implicit.
Set Printing Universes.

Module OneOfType.

  (** This universe will be created each time the functor is instantiated *)
  Definition TypeR := Type.
  Definition TypeS := Type.

  Inductive _option : TypeS :=
  | _Some : TypeR -> _option
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

  Fixpoint pmap_insert (p : positive) (ts : pmap) (x : TypeR) : pmap :=
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

  Record OneOf (ts : pmap) : Type := mkOneOf
  { index : positive
  ; value : match pmap_lookup' ts index return TypeR with
            | _None => Empty_set
            | _Some T => T
            end
  }.

  Definition Into {ts} {T : TypeR} (n : positive)
             (pf : pmap_lookup' ts n = _Some T)
  : T -> OneOf ts :=
    match pf in _ = X return match X return TypeR with
                             | _Some T => T
                             | _None => Empty_set
                             end -> OneOf ts
    with
    | eq_refl => @mkOneOf ts n
    end.

  Fixpoint asNth' {ts : pmap} (p p' : positive)
  : match pmap_lookup' ts p' return TypeR with
    | _None => Empty_set
    | _Some T => T
    end -> option match pmap_lookup' ts p return TypeR with
                  | _None => Empty_set
                  | _Some T => T
                  end :=
  match p as p , p' as p'
        return match pmap_lookup' ts p' return TypeR with
                 | _None => Empty_set
                 | _Some T => T
               end -> option match pmap_lookup' ts p return TypeR with
                             | _None => Empty_set
                             | _Some T => T
                             end
  with
    | xH , xH => Some
    | xI p , xI p' => asNth' p p'
    | xO p , xO p' => asNth' p p'
    | _ , _ => fun _ => None
  end.

  Definition asNth {ts : pmap} (p : positive) (oe : OneOf ts)
  : option match pmap_lookup' ts p return TypeR with
           | _None => Empty_set
           | _Some T => T
           end :=
    @asNth' ts p oe.(index) oe.(value).

  Definition OutOf {ts} {T : Type} (n : positive)
             (pf : pmap_lookup' ts n = _Some T)
  : OneOf ts -> option T :=
    match pf in _ = X
          return OneOf ts -> option match X return TypeR with
                                    | _None => Empty_set
                                    | _Some T => T
                                    end
    with
    | eq_refl => asNth _
    end.

  Global Instance Injective_OneOf m i1 i2 v1 v2
  : Injective (@eq (OneOf m)
                   {| index := i1 ; value := v1 |}
                   {| index := i2 ; value := v2 |}) :=
  { result := exists pf : i2 = i1,
      v1 = match pf in _ = T
                 return match pmap_lookup' m T return TypeR with
                        | _None => Empty_set
                        | _Some T => T
                        end with
           | eq_refl => v2
           end
  ; injection :=fun H =>
      match H in _ = h
            return exists pf : index h = i1 ,
          v1 = match pf in (_ = T)
                     return match pmap_lookup' m T return TypeR with
                            | _Some T0 => T0
                            | _None => Empty_set
                            end
               with
               | eq_refl => value h
               end
      with
      | eq_refl => @ex_intro _ _ eq_refl eq_refl
      end
  }.


  Definition asNth'' (ts : pmap) p (x : OneOf ts)
  : option match pmap_lookup' ts p return TypeR with
           | _Some T => T
           | _None => Empty_set
           end :=
    match Pos.eq_dec (index x) p with
    | left pf' => Some match pf' in _ = X
                             return match pmap_lookup' ts X
                                          return TypeR
                                    with
                                    | _Some T => T
                                    | _None => Empty_set
                                    end
                       with
                       | eq_refl => value x
                       end
    | right _ => None
    end.

  Theorem asNth'_asNth''
  : forall ts p x,
      @asNth' ts p (index x) (value x) = @asNth'' ts p x.
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

  Lemma asNth'_get_lookup : forall p ts v, asNth' (ts:=ts) p p v = Some v.
  Proof.
    induction p; simpl; intros; auto.
  Qed.

  Theorem Outof_Into : forall ts T p pf v,
    @OutOf ts T p pf (@Into ts T p pf v) = Some v.
  Proof using.
    unfold OutOf, Into.
    intros.
    Require Import MirrorCore.Util.Compat.
    autorewrite_with_eq_rw.
    unfold asNth. simpl.
    rewrite asNth'_get_lookup.
    { generalize dependent (pmap_lookup' ts p).
      intros. subst. reflexivity. }
  Qed.

  Theorem Into_OutOf : forall ts T p pf v e,
      @OutOf ts T p pf e = Some v ->
      @Into ts T p pf v = e.
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
      revert value0 y.
      revert index0. revert ts.
      induction p; destruct index0; simpl; intros; try congruence.
      { f_equal. eauto. }
      { f_equal. eauto. } }
    subst.
    rewrite asNth'_get_lookup in H. inv_all. subst.
    f_equal. clear.
    generalize dependent (pmap_lookup' ts index0).
    intros; subst. reflexivity.
  Qed.

End OneOfType.

Import OneOfType.

Section RSym_OneOf.
  Context {typ : Type} {RType_typ : RType typ} {RTypeOk_typ : RTypeOk}.

  Instance RSym_Empty_set : RSym Empty_set :=
  { typeof_sym s := None
  ; symD := fun f => match f return unit with end
  ; sym_eqb := fun f _ => match f return option bool with end
  }.

  Definition typeof_sym_OneOf {m : pmap}
    (H : forall p, RSym match pmap_lookup' m p return TypeR with
                        | _Some T => T
                        | _None => Empty_set
                        end)
    (s : OneOf m) : option typ :=
    match s with
    | mkOneOf _ x v =>
      match pmap_lookup' m x as o return o = pmap_lookup' m x -> option typ with
      | _Some T =>
        fun pf =>
          let RSym_p :=
              eq_rect_r (fun o => RSym match o return TypeR with
                                       | _Some T => T
                                       | _None => Empty_set
                                       end) (H x) pf in
          let v' :=
              eq_rect_r (fun o => match o return TypeR with
                                  | _Some T => T
                                  | _None => Empty_set
                                  end) v pf in
          typeof_sym (RSym := RSym_p) v'
      | _None => fun _ => None
      end eq_refl
    end.

  Definition symD_OneOf (m : pmap)
    (H : forall p, RSym match pmap_lookup' m p return TypeR with
                        | _Some T => T
                        | _None => Empty_set
                        end)
    (f : OneOf m)
  : match typeof_sym_OneOf H f return TypeR with
    | Some t => typD t
    | None => unit
    end.
  refine (
    match f as f' return f = f' ->
                         match typeof_sym_OneOf H f' return TypeR with
                         | Some t => typD t
                         | None => unit:Type
                         end with
    | mkOneOf _ x v =>
      fun eqf =>
        match pmap_lookup' m x as o
              return o = pmap_lookup' m x ->
                     match typeof_sym_OneOf H {| index := x; value := v |}
                           return TypeR
                     with
                     | Some t => typD t
                     | None => unit
                     end with
        | _Some T =>
          fun pf =>
            let RSym_p :=
                eq_rect_r (fun o => RSym match o return TypeR with
                                         | _Some T => T
                                         | _None => Empty_set
                                         end) (H x) pf in
            let v' :=
                eq_rect_r (fun o => match o return TypeR with
                                    | _Some T => T
                                    | _None => Empty_set
                                    end) v pf in
            let v'' := symD (RSym := RSym_p) v' in _
        | _None =>
          fun pf =>
            let RSym_p :=
                eq_rect_r (fun o => RSym match o return TypeR with
                                         | _Some T => T
                                         | _None => Empty_set
                                         end) (H x) pf in
            let v' :=
                eq_rect_r (fun o => match o return TypeR with
                                    | _Some T => T
                                    | _None => Empty_set
                                    end) v pf in _
        end eq_refl
    end eq_refl).
  { unfold typeof_sym_OneOf.
    generalize dependent (H x).
    clear H.
    clear eqf.
    revert v v'.
    rewrite <- pf.
    intros.
    apply v''. }

  { unfold typeof_sym_OneOf.
    generalize dependent (H x).
    clear H eqf.
    revert v v'.
    rewrite <- pf.
    intros.
    exact tt. }
  Defined.

  Definition sym_eqb_OneOf
    (m : pmap)
    (H : forall p, RSym match pmap_lookup' m p return TypeR with
                        | _Some T => T
                        | _None => Empty_set
                        end)
    (f1 f2 : OneOf m) : option bool :=
    match Pos.eq_dec (index f1) (index f2) with
    | left pf =>
      match pf in _ = T
            return RSym match pmap_lookup' m T return TypeR with
                        | _Some T => T
                        | _None => Empty_set
                        end ->
                   match pmap_lookup' m (index f1) return TypeR with
                   | _Some T => T
                   | _None => Empty_set
                   end ->
                   match pmap_lookup' _ T return TypeR with
                   | _Some T => T
                   | _None => Empty_set
                   end ->
                   option bool
      with
      | eq_refl => @sym_eqb _ _ _
      end (H _) (value f1) (value f2)
    | right _ => None
    end.

  Instance RSymOneOf (m : pmap)
    (H : forall p, RSym match pmap_lookup' m p return TypeR with
                        | _Some T => T
                        | _None => Empty_set
                        end)
  : RSym (OneOf m) :=
  { typeof_sym s := typeof_sym_OneOf H s
  ; symD f := symD_OneOf H f
  ; sym_eqb f1 f2 := sym_eqb_OneOf H f1 f2
  }.

  Fixpoint pmap_lookup'_Empty (p : positive) : pmap_lookup' Empty p = _None :=
    match p with
    | xH => eq_refl
    | xO p => pmap_lookup'_Empty p
    | xI p => pmap_lookup'_Empty p
    end.

  Definition OneOf_Empty (f : OneOf Empty) : False.
  Proof.
    destruct f. rewrite pmap_lookup'_Empty in *.
    intuition congruence.
  Defined.

  Instance RSym_Empty : RSym (OneOf Empty) :=
  { typeof_sym s := None
  ; symD := fun f => match OneOf_Empty f return unit with end
  ; sym_eqb := fun f _ => match OneOf_Empty f return option bool with end
  }.

  Instance RSymOk_OneOf (m : pmap)
           (H1 : forall p, RSym match pmap_lookup' m p return TypeR with
                                | _Some T => T
                                | _None => Empty_set
                                end)
           (H2 : forall p, RSymOk (H1 p))
  : RSymOk (RSymOneOf m H1) :=
  { sym_eqbOk f1 f2 :=
      match f1 as f1'
            return match sym_eqb f1' f2 with
                   | Some true => f1' = f2
                   | Some false => f1' <> f2
                   | None => True
                   end
      with
      | mkOneOf _ x1 v1 =>
          match f2 as f2'
                return
                match sym_eqb (mkOneOf _ x1 v1) f2' with
                | Some true => (mkOneOf _ x1 v1) = f2'
                | Some false => (mkOneOf _ x1 v1) <> f2'
                | None => True
                end
          with
          | mkOneOf _ x2 v2 => _
          end
      end
  }.
  simpl. unfold sym_eqb_OneOf. simpl.
  destruct (Pos.eq_dec x1 x2).
  { destruct e.
    generalize (@sym_eqbOk _ _ _ _ (H2 x1) v1 v2).
    destruct (sym_eqb v1 v2); auto.
    { destruct b; intros; subst; auto.
      intro.
      apply H. inv_all.
      rewrite H3. clear - RTypeOk_typ.
      rewrite (UIP_refl x). reflexivity. } }
  { trivial. }
  Defined.

End RSym_OneOf.
