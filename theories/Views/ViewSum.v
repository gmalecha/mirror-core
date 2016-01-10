Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.syms.SymSum.

Section sum.
  Context {typ : Type}.
  Context {RT : @RType typ}.
  Context {T U V : Type}.

  Context {RSt : RSym T} {RSu : RSym U} {RSv : RSym V}.

  Definition FuncView_left (FV_TU : FuncView U T)
  : FuncView (U + V) T :=
  {| f_insert := fun x => inl (f_insert x)
   ; f_view := fun x => match x with
                        | inl x => f_view x
                        | _ => vNone
                        end |}.

  Theorem FuncViewOk_left (FV : FuncView U T) (FVo : FuncViewOk _ _ _)
  : @FuncViewOk _ _ (@FuncView_left FV) _ _ (RSym_sum RSu RSv) _.
  Proof.
    constructor.
    { simpl. destruct f; simpl.
      { intros. rewrite fv_ok. split; congruence. }
      { split; inversion 1. } }
    { simpl. intros. rewrite fv_compat. reflexivity. }
  Qed.

  Definition FuncView_right (FV_TU : FuncView U T)
  : FuncView (V + U) T :=
  {| f_insert := fun x => inr (f_insert x)
   ; f_view := fun x => match x with
                        | inr x => f_view x
                        | _ => vNone
                        end |}.

  Theorem FuncViewOk_right (FV : FuncView U T) (FVo : FuncViewOk _ _ _)
  : @FuncViewOk _ _ (@FuncView_right FV) _ _ (RSym_sum RSv RSu) _.
  Proof.
    constructor.
    { simpl. destruct f; simpl.
      { split; inversion 1. }
      { intros. rewrite fv_ok. split; congruence. } }
    { simpl. intros. rewrite fv_compat. reflexivity. }
  Qed.

End sum.