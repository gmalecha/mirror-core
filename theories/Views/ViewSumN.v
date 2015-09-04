Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.syms.SymOneOf.
Require Import MirrorCore.Views.FuncView.

Set Printing Universes.

Section FuncViewSumN.
  Context {A func : Type}.

  Global Instance FuncViewPMap (p : positive) (m : OneOfType.pmap)
	 (pf : OneOfType._Some A = OneOfType.pmap_lookup' m p)
  : FuncView (OneOfType.OneOf m) A :=
  { f_insert := @OneOfType.Into m _ p (eq_sym pf)
  ; f_view   :=
      let view := @OneOfType.OutOf m _ _ (eq_sym pf) in
      fun x =>
        match view x with
        | None => vNone
        | Some x => vSome x
        end
  }.

  Variable typ : Type.
  Variable RType_typ : RType typ.

  Require Import MirrorCore.Util.Compat.

  Global Instance FuncViewOkPMap
         (p : positive) (m : OneOfType.pmap)
         (syms : forall p : positive,
             RSym match OneOfType.pmap_lookup' m p return OneOfType.TypeR with
                  | OneOfType._Some T => T
                  | OneOfType._None => Empty_set
                  end)
	 (pf : OneOfType._Some A = OneOfType.pmap_lookup' m p)
         (RSa : RSym A)
  : FuncViewOk (FuncViewPMap p m pf) (RSymOneOf _ _) RSa.
  Proof.
    constructor.
    { unfold f_view, f_insert; simpl.
      clear. intros.
      split.
      { consider (OneOfType.OutOf p (eq_sym pf) f); intros; try congruence.
        inversion H0; clear H0; subst.
        eauto using OneOfType.Into_OutOf. }
      { intros.
        subst.
        rewrite OneOfType.Outof_Into. reflexivity. } }
    { admit. }
  Admitted.

End FuncViewSumN.
