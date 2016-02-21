Require Import ExtLib.Tactics.
Require Import ExtLib.Data.POption.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.syms.SymProd.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.
Set Universe Polymorphism.

Section PartialView.
  Universes s t.
  Variables func A : Type@{s}.

  Class PartialView : Type@{s} :=
  { f_insert : A -> func
  ; f_view : func -> poption A
  }.

  Variable FV : PartialView.
  Variable R : func -> A -> Prop.

  Class PartialViewOk : Type :=
  { pv_ok : forall f a, f_view f = pSome a <-> f_insert a = f
  ; pv_compat : forall (a : A), R (f_insert a) a
  }.

  Lemma pv_okL {FVO : PartialViewOk} f a (H : f_view f = pSome a) :
    f_insert a = f.
  Proof using.
    apply pv_ok; assumption.
  Qed.

  Section ptrns.
    Universe X L.
    Context {T : Type@{X}}.

    Definition ptrn_view (p : ptrn@{X X L} A T)
    : ptrn@{s X L} func T :=
      fun e _T good bad =>
        match f_view e with
        | pNone => bad e
        | pSome f => p f _T good (fun _ => bad e)
        end.

    Global Instance ptrn_view_ok (p : ptrn A T)
    : ptrn_ok p -> ptrn_ok (ptrn_view p).
    Proof.
      unfold ptrn_view, ptrn_ok, Succeeds, Fails.
      intros.
      destruct (f_view x).
      { specialize (H a).
        destruct H.
        { left. destruct H. exists x0.
          setoid_rewrite H. reflexivity. }
        { right. setoid_rewrite H. reflexivity. } }
      { eauto. }
    Qed.

    Context {PVO : PartialViewOk}.

    Theorem Succeeds_ptrn_view (p : ptrn A T) x res (H : ptrn_ok p)
      : Succeeds x (ptrn_view p) res ->
        exists f, f_insert f = x /\ Succeeds f p res.
    Proof.
      unfold Succeeds, ptrn_view. intros.
      destruct (f_view x) eqn:Heq.
      { eapply pv_ok in Heq.
        eexists; split. eassumption.
        destruct (H a).
        { destruct H1. red in H1. setoid_rewrite H1 in H0.
          setoid_rewrite H1. eauto. }
        { red in H1. setoid_rewrite H1 in H0.
          specialize (H0 _ (fun _ => true) (fun _ => false)); inversion H0. } }
      { exfalso.
        specialize (H0 _ (fun _ => true) (fun _ => false)); inversion H0. }
    Qed.

    Global Instance SucceedsE_ptrn_view x res
           (p : ptrn A T) (pok : ptrn_ok p)
    : SucceedsE x (ptrn_view p) res :=
    { s_result := exists f : A, _ /\ Succeeds f p res
    ; s_elim := Succeeds_ptrn_view pok }.

  End ptrns.

End PartialView.

Definition PartialView_id {T : Type} : PartialView T T :=
{| f_insert := fun x => x
 ; f_view := @pSome _ |}.

Theorem PartialViewOk_id {T} (R : T -> T -> Prop) (ReflR : Reflexive R)
: @PartialViewOk T T (@PartialView_id T) R.
Proof.
  constructor.
  { split. inversion 1. reflexivity.
    intros; subst; reflexivity. }
  { simpl. reflexivity. }
Defined.

Definition PartialView_trans {A B C : Type}
           (FVab : PartialView A B) (FVbc : PartialView B C) :
  PartialView A C := {|
    f_insert := fun a => f_insert (f_insert a);
    f_view :=
    fun a =>
      match f_view a with
      | pSome b => f_view b
      | pNone => pNone
      end
  |}.

Section Rcompose.
  Context {A B C : Type}.
  Variable Rab : A -> B -> Prop.
  Variable Rbc : B -> C -> Prop.
  Inductive Rcompose (a : A) (c : C) : Prop :=
  | Rcomposed : forall b, Rab a b -> Rbc b c -> Rcompose a c.
End Rcompose.

Theorem PartialView_transOk {A B C : Type} {Rab} {Rbc}
        (FVab : PartialView A B) (FVbc : PartialView B C)
        (FVabOk : @PartialViewOk _ _ FVab Rab)
        (FVbcOk : @PartialViewOk _ _ FVbc Rbc) :
  @PartialViewOk _ _ (@PartialView_trans A B C FVab FVbc)
                 (Rcompose Rab Rbc).
Proof.
  constructor.
  { split; intros.
    { destruct FVabOk as [? _]; destruct FVbcOk as [? _]; simpl in *.
      remember (f_view f) as o; destruct o; [|congruence].
      apply pv_ok0.
      firstorder congruence. }
    { destruct FVabOk as [? _]; destruct FVbcOk as [? _]; simpl in *.
      apply pv_ok0 in H. rewrite H.
      firstorder congruence. } }
  { intros.
    destruct FVabOk as [_ ?]; destruct FVbcOk as [_ ?]; simpl in *.
    econstructor; [ eapply pv_compat0 | eapply pv_compat1 ]. }
Qed.

(** TODO(gmalecha): Unnecessary
Section FuncViewProd.
  Context {A B C D typ : Type}.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {RSA : RSym A} {RSB : RSym B} {RSC : RSym C} {RSD : RSym D}.
  Context {FVab : FuncView A B}.
  Context {FVcd : FuncView C D}.
  Context {FVabOk : @FuncViewOk _ _ FVab typ _ _ _}.
  Context {FVcdOk : @FuncViewOk _ _ FVcd typ _ _ _}.

  Context {Typ2Prod : Typ2 _ prod}.

  Global Instance FuncView_prod : FuncView (A * C) (B * D) := {
    f_insert := fun p => (f_insert (fst p), f_insert (snd p));
    f_view :=
      fun p =>
        match f_view (fst p), f_view (snd p) with
        | pSome a, pSome b => pSome (a, b)
        | _, _ => pNone
        end
  }.

  Theorem FuncView_prodOk
  : @FuncViewOk _ _ FuncView_prod typ RType_typ _ _.
  Proof.
    constructor.
    { intros; destruct f, a; simpl in *; split; intros.
      { destruct FVabOk as [? _]; destruct FVcdOk as [? _]; simpl in *.
        remember (f_view a0) as o1; remember (f_view c) as o2.
        destruct o1, o2; try congruence. inversion H; subst.
        f_equal; [apply fv_ok0; rewrite Heqo1 | apply fv_ok1; rewrite Heqo2]; reflexivity. }
      { inversion H; subst.
        destruct FVabOk as [? _]; destruct FVcdOk as [? _]; simpl in *.
        specialize (fv_ok0 (f_insert b) b).
        destruct fv_ok0 as [_ ?]. specialize (H0 eq_refl). rewrite H0.
        specialize (fv_ok1 (f_insert d) d).
        destruct fv_ok1 as [_ ?]. specialize (H1 eq_refl). rewrite H1.
        reflexivity. } }
    { intros; destruct a.
      destruct FVabOk as [_ ?]; destruct FVcdOk as [_ ?]; simpl in *.
      unfold RSymProd, symAs, typeof_prod in *. simpl in *.
      specialize (fv_compat0 b); specialize (fv_compat1 d).
      generalize dependent (symD (f_insert b)).
      generalize dependent (symD (f_insert d)).
      rewrite fv_compat_typ; eauto with typeclass_instances.
      rewrite fv_compat_typ; eauto with typeclass_instances.
      generalize dependent (symD b).
      generalize dependent (symD d).
      destruct (typeof_sym b); destruct (typeof_sym d); intros; auto.
      { intros.
        specialize (fv_compat1 t1).
        specialize (fv_compat0 t0).
        destruct (type_cast t (typ2 t0 t1)); auto.
        rewrite type_cast_refl in *; eauto.
        compute in fv_compat1, fv_compat0.
        inv_all. subst. reflexivity. } }
  Qed.

End FuncViewProd.
**)