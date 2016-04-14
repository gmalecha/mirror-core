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

(** * Partial Views **)
(** This file defines PartialViews which allows you to 'view' one type
 ** as another type.
 ** TODO:
 ** The related concept in Haskell is a Prism. It would be great to
 ** leverage that work, but I'm not certain how to reason about it.
 **)

Section PartialView.
  Universes s.
  Variable func A : Type@{s}.

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

Theorem PartialViewOk_id_eq {T}
: @PartialViewOk T T (@PartialView_id T) (@eq T).
Proof. eapply PartialViewOk_id. eauto. Defined.

Definition PartialView_trans {A B C : Type}
           (FVab : PartialView A B) (FVbc : PartialView B C)
: PartialView A C :=
{| f_insert := fun a => f_insert (f_insert a);
   f_view :=
     fun a =>
       match f_view a with
       | pSome b => f_view b
       | pNone => pNone
       end
 |}.

Theorem PartialView_transOk {A B C : Type} {Rab} {Rbc} {Rabc : _ -> _ -> Prop}
        (FVab : PartialView A B) (FVbc : PartialView B C)
        (FVabOk : @PartialViewOk _ _ FVab Rab)
        (FVbcOk : @PartialViewOk _ _ FVbc Rbc)
        (Rabc_factors : forall a b c, Rab a b -> Rbc b c -> Rabc a c):
  @PartialViewOk _ _ (@PartialView_trans A B C FVab FVbc)
                 Rabc.
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
    eapply Rabc_factors; [ eapply pv_compat0 | eapply pv_compat1 ]. }
Defined.

Section PartialViewProd.
  Polymorphic Context {A B C D : Type}.
  Polymorphic Context {FVab : PartialView A B}.
  Polymorphic Context {FVcd : PartialView C D}.
  Polymorphic Context {Rab : A -> B -> Prop} {Rcd : C -> D -> Prop}.
  Polymorphic Context {FVabOk : @PartialViewOk _ _ FVab Rab}.
  Polymorphic Context {FVcdOk : @PartialViewOk _ _ FVcd Rcd}.

  Global Polymorphic Instance PartialView_prod : PartialView (A * C) (B * D) :=
  { f_insert := fun p => (f_insert (fst p), f_insert (snd p));
    f_view :=
      fun p =>
        match f_view (fst p), f_view (snd p) with
        | pSome a, pSome b => pSome (a, b)
        | _, _ => pNone
        end
  }.

  (** TODO(gmalecha): Move this to ExtLib.Data.Prod **)
  Inductive Rpair (x : A * C) (y : B * D) : Prop :=
  | Rpair_pair : Rab (fst x) (fst y) ->
                 Rcd (snd x) (snd y) -> Rpair x y.

  Polymorphic Theorem PartialViewOk_prod
  : @PartialViewOk _ _ PartialView_prod Rpair.
  Proof.
    constructor.
    { intros; destruct f, a; simpl in *; split; intros.
      { destruct FVabOk as [? _]; destruct FVcdOk as [? _]; simpl in *.
        specialize (pv_ok0 a0).
        specialize (pv_ok1 c).
        destruct (f_view a0); destruct (f_view c); try congruence.
        f_equal; [ eapply pv_ok0 | eapply pv_ok1 ]; congruence. }
      { inversion H; clear H; subst.
        rewrite (proj2 (pv_ok _ b) eq_refl).
        rewrite (proj2 (pv_ok _ d) eq_refl).
        reflexivity. } }
    { destruct a; simpl; constructor; simpl.
      eapply FVabOk.
      eapply FVcdOk. }
  Qed.

End PartialViewProd.
