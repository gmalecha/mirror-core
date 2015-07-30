Require Import ExtLib.Data.Map.FMapPositive.
Require Import ExtLib.Data.SumN.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.syms.SymOneOf.
Require Import MirrorCore.Views.FuncView.

Section FuncViewSumN.
  Context {A func : Type}.

  Global Instance FuncViewPMap (p : positive) (m : FMapPositive.pmap Type)
	 (pf : Some A = pmap_lookup' m p)
  : FuncView (OneOf m) A :=
  { f_insert := @Into m _ p (eq_sym pf)
  ; f_view   :=
      let view := @OutOf m _ _ (eq_sym pf) in
      fun x =>
        match view x with
        | None => vNone
        | Some x => vSome x
        end
  }.

  Variable typ : Type.
  Variable RType_typ : RType typ.

  Require Import MirrorCore.Util.Compat.

  Definition asNth'' ts p (x : OneOf ts)
  : option match pmap_lookup' ts p with
           | Some T => T
           | None => Empty_set:Type
           end :=
    match Pos.eq_dec (index _ x) p with
    | left pf' => Some match pf' in _ = X return match pmap_lookup' ts X with
                                                 | Some T => T
                                                 | None => Empty_set:Type
                                                 end
                       with
                       | eq_refl => value _ x
                       end
    | right _ => None
    end.

  Theorem asNth'_asNth''
  : forall ts p x,
      @asNth' ts p (index _ x) (value _ x) = @asNth'' ts p x.
  Proof using.
    destruct x. unfold asNth''. simpl.
    destruct (Pos.eq_dec index p); subst.
    { revert value; revert ts.
      induction p; simpl; intros; eauto. }
    { revert value; revert ts; generalize dependent index.
      induction p; destruct index; simpl; intros; eauto.
      { assert (index <> p) by congruence.
        eauto. }
      { assert (index <> p) by congruence.
        eauto. }
      { congruence. } }
  Qed.

  Theorem Outof_Into : forall ts T p pf v,
    @OutOf ts T p pf (@Into ts T p pf v) = Some v.
  Proof using.
  Admitted.

  Theorem Into_OutOf : forall ts T p pf v e,
      @OutOf ts T p pf e = Some v ->
      @Into ts T p pf v = e.
  Proof using.
    unfold OutOf. unfold Into.
    intros. revert H.
    autorewrite_with_eq_rw.
  Admitted.

  Global Instance FuncViewOkPMap
         (p : positive) (m : FMapPositive.pmap Type)
         (syms : forall p : positive,
             RSym match pmap_lookup' m p with
                  | Some T => T
                  | None => Empty_set
                  end)
	 (pf : Some A = pmap_lookup' m p)
         (RSa : RSym A)
  : FuncViewOk (FuncViewPMap p m pf) (RSymOneOf _ _) RSa.
  Proof.
    constructor.
    { unfold f_view, f_insert; simpl.
      clear. intros.
      split.
      { consider (OutOf A p (eq_sym pf) f); intros; try congruence.
        inversion H0; clear H0; subst.
        eauto using Into_OutOf. }
      { intros.
        subst.
        rewrite OutOf_Into. reflexivity. } }
    { admit. }
  Admitted.

End FuncViewSumN.