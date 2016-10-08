Require Import ExtLib.Data.Positive.
Require Import ExtLib.Data.PList.
Require Import ExtLib.Data.Eq.UIP_trans.
Require Import ExtLib.Tactics.

Require Import MirrorCore.MTypes.ModularTypes.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Util.Compat.

Set Implicit Arguments.
Set Strict Implicit.

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

  Record OneOfF (ts : pmap) (x : nat) : Type := mkOneOfF
  { indexF : positive
  ; valueF : type_nth ts indexF x
  }.

  Definition IntoF {ts} {T : nat -> TypeR} x (n : positive)
             (pf : pmap_lookup' ts n = _Some T)
  : T x -> OneOfF ts x :=
    match pf in _ = X return match X return TypeR with
                             | _Some T => T x
                             | _None => Empty_set
                             end -> OneOfF ts x
    with
    | eq_refl => @mkOneOfF ts x n
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

  Definition asNth {ts : pmap} {n} (p : positive) (oe : OneOfF ts n)
  : option (type_nth ts p n) :=
    @asNth' ts n p oe.(indexF) oe.(valueF).

  Definition OutOfF {ts} {T : nat -> TypeR} {x} (n : positive)
             (pf : pmap_lookup' ts n = _Some T)
  : OneOfF ts x -> option (T x) :=
    match pf in _ = X
          return OneOfF ts x ->
                 option match X return TypeR with
                        | _None => Empty_set
                        | _Some T => T x
                        end
    with
    | eq_refl => asNth _
    end.

  Global Instance Injective_OneOf n m i1 i2 v1 v2
  : Injective (@eq (OneOfF m n)
                   {| indexF := i1 ; valueF := v1 |}
                   {| indexF := i2 ; valueF := v2 |}) :=
  { result := exists pf : i2 = i1,
      v1 = match pf in _ = T
                 return type_nth m T n
           with
           | eq_refl => v2
           end
  ; injection := fun H =>
      match H in _ = h
            return exists pf : indexF h = i1 ,
          v1 = match pf in (_ = T)
                     return type_nth m T n
               with
               | eq_refl => valueF h
               end
      with
      | eq_refl => @ex_intro _ _ eq_refl eq_refl
      end
  }.


  Definition asNth'' {ts : pmap} {n} p (x : OneOfF ts n)
  : option (type_nth ts p n) :=
    match Pos.eq_dec (indexF x) p with
    | left pf' => Some match pf' in _ = X
                             return type_nth ts X n
                       with
                       | eq_refl => valueF x
                       end
    | right _ => None
    end.

  Theorem asNth'_asNth''
  : forall ts n p x,
      @asNth' ts n p (indexF x) (valueF x) = @asNth'' ts n p x.
  Proof using.
    destruct x. unfold asNth''. simpl.
    destruct (Pos.eq_dec indexF0 p); subst.
    { revert valueF0; revert ts.
      induction p; simpl; intros; eauto. }
    { revert valueF0; revert ts; generalize dependent indexF0.
      induction p; destruct indexF0; simpl; intros; eauto.
      { assert (indexF0 <> p) by congruence.
        eauto. }
      { assert (indexF0 <> p) by congruence.
        eauto. }
      { congruence. } }
  Qed.

  Lemma asNth'_get_lookup
  : forall n p ts v, asNth' (ts:=ts) (n:=n) p p v = Some v.
  Proof.
    induction p; simpl; intros; eauto.
  Defined.

  Require Import MirrorCore.Util.Compat.

  Theorem OutofF_IntoF : forall n ts T p pf v,
    @OutOfF ts n T p pf (@IntoF ts n T p pf v) = Some v.
  Proof using.
    unfold OutOfF, IntoF.
    intros.
    autorewrite_with_eq_rw.
    unfold asNth. simpl.
    rewrite asNth'_get_lookup.
    { generalize dependent (pmap_lookup' ts p).
      intros. subst. reflexivity. }
  Defined.

  Theorem asNth_eq
    : forall ts n p oe v,
      @asNth ts n p oe = Some v ->
      oe = {| indexF := p ; valueF := v |}.
  Proof.
    unfold asNth.
    destruct oe; simpl.
    revert valueF0. revert indexF0. revert ts.
    induction p; destruct indexF0; simpl; intros;
    try congruence; eapply IHp in H; inv_all; subst; reflexivity.
  Defined.

  Theorem IntoF_OutOfF : forall ts n T p pf v e,
      @OutOfF ts n T p pf e = Some v ->
      @IntoF ts n T p pf v = e.
  Proof using.
    unfold OutOfF, IntoF.
    intros. revert H.
    autorewrite_with_eq_rw.
    unfold asNth.
    destruct e; simpl in *.
    intro.
    assert (p = indexF0).
    { destruct (asNth' p indexF0 valueF0) eqn:?; try congruence.
      inv_all. subst.
      clear - Heqo.
      revert Heqo.
      revert valueF0 t.
      revert indexF0. revert ts.
      induction p; destruct indexF0; simpl; intros; try congruence.
      { f_equal. eauto. }
      { f_equal. eauto. } }
    subst.
    rewrite asNth'_get_lookup in H. inv_all. subst.
    f_equal. clear.
    unfold type_nth in *.
    destruct pf. reflexivity.
  Defined.

  Universe UPmap.
  Polymorphic Fixpoint list_to_pmap_aux
              (lst : plist@{UPmap} (nat -> TypeR)) (p : positive) : pmap :=
    match lst with
    | pnil => OneOfType.Empty
    | pcons x xs => OneOfType.pmap_insert p (list_to_pmap_aux xs (p + 1)) x
  end.

  Definition list_to_pmap (lst : plist@{UPmap} (nat -> TypeR)) :=
    list_to_pmap_aux lst 1.

End OneOfType.

Import OneOfType.

Section TSym_OneOf.
  Context {typ : nat -> Type} {TS : TSym typ}.

  Definition TSym_Empty_set : TSym (fun _ => Empty_set) :=
  {| symbolD := fun n (x : Empty_set) => match x with end
   ; symbol_dec := fun _ x _ => match x with end
   |}.

  Definition TSym_All m : Type :=
    forall p, TSym (type_nth m p).

  Instance TSymOneOf (m : pmap) (H : TSym_All m)
  : TSym (OneOfF m) :=
  { symbolD := fun s x => let ts := H x.(indexF) in
                          @symbolD _ ts _ x.(valueF)
  ; symbol_dec := fun _ a b =>
    match a as a , b as b return {a = b} + {a <> b} with
    |   {| indexF := i1 ; valueF := v1 |}
      , {| indexF := i2 ; valueF := v2 |} =>
        match Pos.eq_dec i1 i2 with
        | left pf =>
          match pf in _ = Z return forall x : type_nth _ Z _,
              {mkOneOfF m _ i1 v1 = mkOneOfF m _ Z x} +
              {mkOneOfF m _ i1 v1 <> mkOneOfF m _ Z x}
          with
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
    change (indexF {| indexF := i1; valueF := v1 |} =
            indexF {| indexF := i2; valueF := v2 |}).
    rewrite H0. reflexivity. }
  Defined.

  Definition TSym_All_Empty : TSym_All Empty.
  Proof.
    red. intros.
    induction p; unfold type_nth in *; simpl; eauto.
    eapply TSym_Empty_set.
  Defined.

  Definition TSym_All_Branch_None l r
  : TSym_All l -> TSym_All r -> TSym_All (Branch _None l r).
  Proof.
    red. intros.
    destruct p.
    { apply X0. }
    { apply X. }
    { apply TSym_Empty_set. }
  Defined.

  Definition TSym_All_Branch_Some s l r
  : TSym s -> TSym_All l -> TSym_All r -> TSym_All (Branch (_Some s) l r).
  Proof.
    red. intros.
    destruct p.
    { apply X1. }
    { apply X0. }
    { assumption. }
  Defined.

  Definition PartialViewPMap_Type (A : nat -> TypeR) (p : positive) (m : pmap)
             (pf : _Some A = pmap_lookup' m p) (n : nat)
  : PartialView (OneOfF m n) (A n) :=
  {| f_insert := IntoF n p (eq_sym pf)
   ; f_view := let view := OutOfF p (eq_sym pf) in
               fun x : OneOfF m n =>
                 match view x with
                 | Some x0 => POption.pSome x0
                 | None => POption.pNone
                 end |}.

  Definition PartialViewOk_TSymOneOf (m : pmap) (H : TSym_All m)
             (p : positive) Z (pf : _Some Z = pmap_lookup' m p)
             n
  : let X : TSym Z := match eq_sym pf in _ = K
                            return TSym (fun n => match K return TypeR with
                                                  | _Some T => T n
                                                  | _None => Empty_set
                                                  end)
                      with
                      | eq_refl => H p
                      end in
    PartialViewOk (PartialViewPMap_Type p m pf n)
                  (fun a b =>
                     @symbolD _ (TSymOneOf H) _ a = symbolD b).
  Proof.
    constructor.
    { simpl; intros.
      split.
      { intros.
        generalize (@IntoF_OutOfF m _ n p (eq_sym pf) a f).
        destruct (OutOfF p (eq_sym pf) f).
        { intro. apply H1.
          clear - H0. f_equal. injection H0. tauto. }
        { inversion H0. } }
      { intros. subst.
        rewrite OutofF_IntoF. reflexivity. } }
    { simpl. unfold IntoF.
      intros. unfold type_nth.
      simpl.
      autorewrite_with_eq_rw.
      simpl.
      generalize (H p). clear. unfold type_nth.
      destruct pf. reflexivity. }
  Defined.

  Fixpoint pmap_lookup'_Empty (p : positive) : pmap_lookup' Empty p = _None :=
    match p with
    | xH => eq_refl
    | xO p => pmap_lookup'_Empty p
    | xI p => pmap_lookup'_Empty p
    end.

End TSym_OneOf.
