Require Import ExtLib.Tactics.
Require Import ExtLib.Data.POption.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.syms.SymProd.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Section FuncView.
  Polymorphic Universes s t.
  Polymorphic Variables func A : Type@{s}.

  Polymorphic Class FuncView : Type@{s} :=
  { f_insert : A -> func
  ; f_view : func -> poption A
  }.

  Polymorphic Variable FV : FuncView.

  Polymorphic Variable typ : Type@{t}.
  Polymorphic Variable RType_typ : RType typ.
  Polymorphic Variable Sym_func : RSym func.
  Polymorphic Variable Sym_A : RSym A.

  Polymorphic Class FuncViewOk : Type :=
  { fv_ok : forall f a, f_view f = pSome a <-> f_insert a = f
  ; fv_compat : forall (a : A) t,
      symAs a t = symAs (f_insert a) t
  }.

  Polymorphic Lemma fv_okL {FVO : FuncViewOk} f a (H : f_view f = pSome a) :
    f_insert a = f.
  Proof using.
    apply fv_ok; assumption.
  Qed.

  Polymorphic Variable RTypeOk_typ : RTypeOk.

  Polymorphic Theorem fv_compat_typ (FVO : FuncViewOk)
  : forall a, typeof_sym (f_insert a) = typeof_sym a.
  Proof using RTypeOk_typ.
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

  Polymorphic Theorem fv_compat_val (FVO : FuncViewOk)
  : forall (a : A),
        symD a = match fv_compat_typ _ a in _ = T return match T with
                                                         | Some t => typD t
                                                         | None => unit:Type
                                                         end
                 with
                 | eq_refl => symD (f_insert a)
                 end.
  Proof using.
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

  Polymorphic Lemma fv_typeof_sym {FVO : FuncViewOk} f p t v
    (Hview : f_view f = pSome p) (Hfunc : symAs f t = Some v) :
    typeof_sym p = Some t.
  Proof using.
    destruct (fv_ok f p) as [H _].
    specialize (H Hview); subst.
    rewrite <- fv_compat in Hfunc.
    unfold symAs in Hfunc.
    generalize dependent (symD p).
    destruct (typeof_sym p); intros; [|congruence].
    forward.
  Defined.

  Polymorphic Variable FVO : FuncViewOk.

  Global Polymorphic Instance Injective_exprD'_f_insert (a : A) (t : typ) (v : typD t)
  : Injective (symAs (f_insert a) t = Some v) :=
  { result := symAs a t = Some v
  ; injection := fun H => _
  }.
  Proof.
    rewrite fv_compat; assumption.
  Defined.

  Polymorphic Lemma symAs_finsertI (t : typ) (f : A)
        (P : option (typD t) -> Prop)
        (H : P (symAs f t)) :
    P (symAs (f_insert f) t).
  Proof.
    rewrite <- fv_compat; assumption.
  Qed.

  Section ptrns.
  Polymorphic Universe X L.
  Context {T : Type@{X}}.

  Polymorphic Definition ptrn_view (p : ptrn@{X X L} A T)
  : ptrn@{s X L} func T :=
    fun e _T good bad =>
      match f_view e with
      | pNone => bad e
      | pSome f => p f _T good (fun _ => bad e)
      end.

  Global Polymorphic Instance ptrn_view_ok (p : ptrn A T)
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

  Polymorphic Theorem Succeeds_ptrn_view (p : ptrn A T) x res (H : ptrn_ok p)
  : Succeeds x (ptrn_view p) res ->
    exists f, f_insert f = x /\ Succeeds f p res.
  Proof using RTypeOk_typ Sym_func Sym_A FVO.
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

  Global Polymorphic Instance ptrn_view_SucceedsE
         {x : func} {res : T} {p : ptrn A T}
         {Sym_A : RSym A}
         {pok : ptrn_ok p}
  : SucceedsE x (ptrn_view p) res :=
  { s_result := exists f : A, f_insert f = x /\ Succeeds f p res
  ; s_elim := @Succeeds_ptrn_view p x res _
  }.
  End ptrns.

End FuncView.


Definition FuncView_id {T : Type} : FuncView T T :=
{| f_insert := fun x => x
 ; f_view := @pSome _ |}.

Theorem FuncViewOk_id {T typ} (RT : RType typ) (RS : RSym T)
: @FuncViewOk T T (@FuncView_id T) typ _ _ _.
Proof.
  constructor.
  { split. inversion 1. reflexivity.
    intros; subst; reflexivity. }
  { simpl. reflexivity. }
Defined.

Definition FuncView_trans {A B C : Type} (FVab : FuncView A B) (FVbc : FuncView B C) :
  FuncView A C := {|
    f_insert := fun a => f_insert (f_insert a);
    f_view := 
    fun a =>
      match f_view a with 
      | pSome b => f_view b
      | pNone => pNone
      end
  |}.

Theorem FuncView_transOk {A B C typ : Type} 
        {RType_typ : RType typ}
        {RSA : RSym A} {RSB : RSym B} {RSC : RSym C}
        (FVab : FuncView A B) (FVbc : FuncView B C) 
        (FVabOk : @FuncViewOk _ _ FVab typ _ _ _) 
        (FVbcOk : @FuncViewOk _ _ FVbc typ _ _ _) :
  @FuncViewOk _ _ (@FuncView_trans A B C FVab FVbc) typ _ _ _.
Proof.
  constructor.
  { split; intros.
    { destruct FVabOk as [? _]; destruct FVbcOk as [? _]; simpl in *.
      remember (f_view f) as o; destruct o; [|congruence].
      apply fv_ok0.
      firstorder congruence. }
    { destruct FVabOk as [? _]; destruct FVbcOk as [? _]; simpl in *.
      apply fv_ok0 in H. rewrite H.
      firstorder congruence. } }
  { intros.
    destruct FVabOk as [_ ?]; destruct FVbcOk as [_ ?]; simpl in *.
    firstorder congruence. }
Qed.
    
Section FuncViewProd.
  Context {A B C D typ : Type}.
  Context {RType_typ : RType typ}.
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
(*
  Theorem FuncView_prodOk :
  @FuncViewOk _ _ FuncView_prod typ RType_typ _ _.
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
    clear -fv_compat0 fv_compat1.
    specialize (fv_compat0 b t); specialize (fv_compat1 d t).
    generalize dependent (f_insert b).
    generalize dependent (f_insert d).
    intros.
    unfold symAs in *; simpl in *.
    revert fv_compat1. revert fv_compat0.
    simpl.
    unfold typeof_prod; simpl.
    generalize dependent (symD a).
    generalize dependent (symD b).
    generalize dependent (symD c).
    generalize dependent (symD d).
    generalize dependent (typeof_sym a).
    generalize dependent (typeof_sym b).
    generalize dependent (typeof_sym c).
    generalize dependent (typeof_sym d).
    intros. destruct o, o0, o1, o2; simpl; try reflexivity.

    admit.
Admitted.

*)

End FuncViewProd.