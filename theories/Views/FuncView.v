Require Import ExtLib.Tactics.
Require Import ExtLib.Data.POption.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Views.View.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.syms.SymProd.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.
Set Universe Polymorphism.

Section FuncView.
  Universes s t.
  Variables func A : Type@{s}.
  Variable FV : PartialView func A.
  Variable typ : Type@{t}.
  Variable RType_typ : RType typ.
  Variable Sym_func : RSym func.
  Variable Sym_A : RSym A.

(*  Definition FuncView := PartialView func A. *)

  Definition func_equiv (f : func) (a : A) : Prop :=
    forall t, symAs a t = symAs f t.

  Definition FuncViewOk : Type :=
    PartialViewOk FV func_equiv.

  Variable FVO : FuncViewOk.

  Theorem fv_ok : forall f a, f_view f = pSome a <-> f_insert a = f.
  Proof. exact (@pv_ok _ _ _ _ FVO). Qed.

  Theorem fv_compat : forall (a : A) t,
      symAs a t = symAs (f_insert a) t.
  Proof. exact (@pv_compat _ _ _ _ FVO). Qed.

  Lemma fv_okL f a (H : f_view f = pSome a) :
    f_insert a = f.
  Proof using FVO.
    apply fv_ok; assumption.
  Qed.

  Variable RTypeOk_typ : RTypeOk.

  Theorem fv_compat_typ
  : forall a, typeof_sym (f_insert a) = typeof_sym a.
  Proof using RTypeOk_typ FVO.
    intros.
    generalize (fv_compat a).
    unfold symAs. intros.
    generalize dependent (symD a).
    generalize dependent (symD (f_insert a)).
    destruct (typeof_sym a).
    { destruct (typeof_sym (f_insert a)).
      { intros.
        specialize (H t).
        rewrite type_cast_refl in H; eauto.
        destruct (type_cast t t0); try solve [ inversion H ].
        inversion H. subst.
        f_equal. symmetry. assumption. }
      { intros.
        specialize (H t).
        rewrite type_cast_refl in H; eauto.
        inversion H. } }
    { intros.
      destruct (typeof_sym (f_insert a)); auto.
      specialize (H t).
      rewrite type_cast_refl in H. inversion H.
      eauto. }
  Defined.

  Theorem fv_compat_val
  : forall (a : A),
        symD a = match fv_compat_typ a in _ = T
                       return match T with
                              | Some t => typD t
                              | None => unit:Type
                              end
                 with
                 | eq_refl => symD (f_insert a)
                 end.
  Proof using FVO.
    intros.
    assert (typeof_sym a = None \/ exists t, typeof_sym a = Some t).
    { clear. destruct (typeof_sym a); eauto. }
    destruct H.
    { generalize (symD a).
      generalize (symD (f_insert a)).
      generalize (fv_compat_typ a).
      rewrite H.
      intro. rewrite e.
      clear. destruct y; destruct y; reflexivity. }
    { destruct H.
      generalize (fv_compat a x).
      unfold symAs.
      generalize dependent (symD a).
      generalize dependent (symD (f_insert a)).
      generalize (fv_compat_typ a).
      destruct e.
      rewrite H.
      setoid_rewrite type_cast_refl; eauto.
      intros.
      inv_all. assumption. }
  Qed.

  Lemma fv_typeof_sym f p t v
    (Hview : f_view f = pSome p) (Hfunc : symAs f t = Some v) :
    typeof_sym p = Some t.
  Proof using FVO.
    destruct (fv_ok f p) as [H _].
    specialize (H Hview); subst.
    rewrite <- fv_compat in Hfunc.
    unfold symAs in Hfunc.
    generalize dependent (symD p).
    destruct (typeof_sym p); intros; [|congruence].
    forward.
  Defined.

  Global Instance Injective_exprD'_f_insert (a : A) (t : typ) (v : typD t)
  : Injective (symAs (f_insert a) t = Some v) :=
  { result := symAs a t = Some v
  ; injection := fun H => _
  }.
  Proof.
    rewrite fv_compat; assumption.
  Defined.

  Lemma symAs_finsertI (t : typ) (f : A)
        (P : option (typD t) -> Prop)
        (H : P (symAs f t)) :
    P (symAs (f_insert f) t).
  Proof.
    rewrite <- fv_compat; assumption.
  Qed.

  Global Instance SucceedsE_FuncView_ptrn_view {T : Type} x res
         (p : ptrn A T) (pok : ptrn_ok p)
  : SucceedsE x (ptrn_view FV p) res :=
  { s_result := exists f : A, _ /\ Succeeds f p res
  ; s_elim := Succeeds_ptrn_view (PVO:=FVO) pok }.

End FuncView.

Theorem FuncViewOk_id {T typ} (RT : RType typ) (RS : RSym T)
: @FuncViewOk T T (@PartialView_id T) typ _ _ _.
Proof.
  constructor.
  { split. inversion 1. reflexivity.
    intros; subst; reflexivity. }
  { simpl. unfold func_equiv. reflexivity. }
Defined.

(*
Global Instance PartialView_FuncView {A B} : FuncView A B -> PartialView A B :=
  fun x => x.
*)

Existing Class FuncViewOk.
Export MirrorCore.Views.View.