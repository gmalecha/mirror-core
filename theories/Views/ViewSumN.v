Require Import ExtLib.Data.Positive.
Require Import ExtLib.Data.POption.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.Compat.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.syms.SymOneOf.
Require Import MirrorCore.Views.FuncView.

Section FuncViewSumN.
  Context {A func : Type}.

  Global Instance FuncViewPMap (p : positive) (m : OneOfType.pmap)
	 (pf : OneOfType._Some A = OneOfType.pmap_lookup' m p)
  : PartialView (OneOfType.OneOf m) A :=
  { f_insert := @OneOfType.Into m _ p (eq_sym pf)
  ; f_view   :=
      let view := @OneOfType.OutOf m _ _ (eq_sym pf) in
      fun x =>
        match view x with
        | None => pNone
        | Some x => pSome x
        end
  }.

  Variable typ : Type.
  Variable RType_typ : RType typ.

  Global Instance FuncViewOkPMap
         (p : positive) (m : OneOfType.pmap)
         (syms : forall p : positive,
             RSym match OneOfType.pmap_lookup' m p return OneOfType.TypeR with
                  | OneOfType._Some T => T
                  | OneOfType._None => Empty_set
                  end)
	 (pf : OneOfType._Some A = OneOfType.pmap_lookup' m p)
  : FuncViewOk (FuncViewPMap p m pf) (RSymOneOf m syms)
               (match eq_sym pf in _ = Z
                      return RSym match Z with
                                  | OneOfType._Some T => T
                                  | OneOfType._None => Empty_set
                                  end
                with
                | eq_refl => syms p
                end).
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
    { simpl. intros.
      unfold OneOfType.Into, RSymOneOf, func_equiv, symAs.
      intros. simpl.
      autorewrite_with_eq_rw.
      unfold symD_OneOf, typeof_sym_OneOf. simpl.
      unfold internal_eq_rew_dep, eq_rect_r, eq_rect. simpl.
      generalize (@symD typ RType_typ).
      generalize (@typeof_sym typ RType_typ).
      generalize (@type_cast typ RType_typ t).
      generalize (syms p).
      destruct pf. reflexivity. }
  Qed.

End FuncViewSumN.
