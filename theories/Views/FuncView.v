Require Import ExtLib.Tactics.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Inductive view_option (A : Type) :=
| vSome : A -> view_option A
| vNone : view_option A.

Arguments vNone {A}.

Section FuncView.
  Variables func A : Type.

  Class FuncView : Type :=
  { f_insert : A -> func
  ; f_view : func -> view_option A
  }.

  Variable FV : FuncView.

  Variable typ : Type.
  Variable RType_typ : RType typ.
  Variable Sym_func : RSym func.
  Variable Sym_A : RSym A.

  Class FuncViewOk : Type :=
  { fv_ok : forall f a, f_view f = vSome a <-> f_insert a = f
  ; fv_compat : forall (a : A) t,
      symAs a t = symAs (f_insert a) t
  }.

  Lemma fv_okL {FVO : FuncViewOk} f a (H : f_view f = vSome a) :
    f_insert a = f.
  Proof.
    apply fv_ok; assumption.
  Qed.

  Variable RTypeOk_typ : RTypeOk.

  Theorem fv_compat_typ (FVO : FuncViewOk)
  : forall a, typeof_sym (f_insert a) = typeof_sym a.
  Proof.
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

  Theorem fv_compat_val (FVO : FuncViewOk)
  : forall (a : A),
        symD a = match fv_compat_typ _ a in _ = T return match T with
                                                         | Some t => typD t
                                                         | None => unit:Type
                                                         end
                 with
                 | eq_refl => symD (f_insert a)
                 end.
  Proof.
    intros.
    assert (typeof_sym a = None \/ exists t, typeof_sym a = Some t).
    { clear. destruct (typeof_sym a); eauto. }
    destruct H.
    { generalize (symD a).
      generalize (symD (f_insert a)).
      generalize (fv_compat_typ FVO a).
      rewrite H.
      intro. rewrite e.
      clear. destruct y; destruct y; reflexivity. }
    { destruct H.
      generalize (fv_compat a x).
      unfold symAs.
      generalize dependent (symD a).
      generalize dependent (symD (f_insert a)).
      generalize (fv_compat_typ FVO a).
      destruct e.
      rewrite H.
      setoid_rewrite type_cast_refl; eauto.
      intros.
      inv_all. assumption. }
  Qed.

  Lemma fv_typeof_sym {FVO : FuncViewOk} f p t v
    (Hview : f_view f = vSome p) (Hfunc : symAs f t = Some v) :
    typeof_sym p = Some t.
  Proof.
    destruct (fv_ok f p) as [H _].
    specialize (H Hview); subst.
    rewrite <- fv_compat in Hfunc.
    unfold symAs in Hfunc.
    generalize dependent (symD p).
    destruct (typeof_sym p); intros; [|congruence].
    forward.
  Defined.

  Definition ptrn_view {T} (p : ptrn A T) : ptrn func T :=
    fun e _T good bad =>
      match f_view e with
      | vNone => bad e
      | vSome f => p f _T good (fun _ => bad e)
      end.

  Global Instance ptrn_view_ok T (p : ptrn A T)
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

  Variable FVO : FuncViewOk.

  Theorem Succeeds_ptrn_view {T} (p : ptrn A T) x res (H : ptrn_ok p)
  : Succeeds x (ptrn_view p) res ->
    exists f, f_insert f = x /\ Succeeds f p res.
  Proof.
    unfold Succeeds, ptrn_view. intros.
    destruct (f_view x) eqn:Heq.
    { eapply fv_ok in Heq.
      eexists; split; eauto.
      destruct (H a).
      { destruct H1. red in H1. setoid_rewrite H1 in H0.
        setoid_rewrite H1. eauto. }
      { red in H1. setoid_rewrite H1 in H0.
        specialize (H0 _ (fun _ => true) (fun _ => false)); inversion H0. } }
    { exfalso.
      specialize (H0 _ (fun _ => true) (fun _ => false)); inversion H0. }
  Qed.

  Global Instance ptrn_view_SucceedsE {T : Type} {x : func} {res : T} {p : ptrn A T} 
         {Sym_A : RSym A}
         {pok : ptrn_ok p}
  : SucceedsE x (ptrn_view p) res :=
  { s_result := exists f : A, f_insert f = x /\ Succeeds f p res
  ; s_elim := @Succeeds_ptrn_view T p x res _
  }.

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

End FuncView.


Definition FuncView_id {T : Type} : FuncView T T :=
{| f_insert := fun x => x
 ; f_view := @vSome _ |}.

Theorem FuncViewOk_id {T typ} (RT : RType typ) (RS : RSym T)
: @FuncViewOk T T (@FuncView_id T) typ _ _ _.
Proof.
  constructor.
  { split. inversion 1. reflexivity.
    intros; subst; reflexivity. }
  { simpl. reflexivity. }
Defined.
