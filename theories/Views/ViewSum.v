Require Import ExtLib.Data.POption.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.syms.SymSum.

Section sum.
  Context {typ : Set}.
  Context {RT : @RType typ}.

  Context {T U V : Set}.
  Context {RSt : RSym T} {RSu : RSym U} {RSv : RSym V}.

  (** This is generic to PartialView **)
  Definition PartialView_left (FV_TU : PartialView U T)
  : PartialView (U + V) T :=
  {| f_insert := fun x => inl (f_insert x)
   ; f_view := fun x => match x with
                        | inl x => f_view x
                        | _ => pNone
                        end |}.

  Theorem PartialViewOk_left (FV : PartialView U T) (FVo : FuncViewOk _ _ _)
  : @FuncViewOk _ _ (@PartialView_left FV) _ _ (RSym_sum RSu RSv) _.
  Proof.
    constructor.
    { simpl. destruct f; simpl.
      { intros. rewrite fv_ok. split; congruence. eassumption. }
      { split; inversion 1. } }
    { simpl. intros. red. eapply fv_compat. eassumption. }
  Qed.

  Definition PartialView_right (FV_TU : PartialView U T)
  : PartialView (V + U) T :=
  {| f_insert := fun x => inr (f_insert x)
   ; f_view := fun x => match x with
                        | inr x => f_view x
                        | _ => pNone
                        end |}.

  Theorem PartialViewOk_right (FV : PartialView U T) (FVo : FuncViewOk _ _ _)
  : @FuncViewOk _ _ (@PartialView_right FV) _ _ (RSym_sum RSv RSu) _.
  Proof.
    constructor.
    { simpl. destruct f; simpl.
      { split; inversion 1. }
      { intros. rewrite fv_ok. split; congruence. eassumption. } }
    { simpl. intros. red. eapply fv_compat. eassumption. }
  Qed.

End sum.