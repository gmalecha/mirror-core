Require Import FunctionalExtensionality.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.AbsAppI.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprD.
Require Import MirrorCore.Lambda.ExprDFacts.
Require Import MirrorCore.Lambda.Red.

Set Implicit Arguments.
Set Strict Implicit.

Section some_lemmas.
  Variable typ : Type.
  Variable sym : Type.
  Variable RType_typ : RType typ.
  Variable RTypeOk : RTypeOk.
  Variable Typ2_arr : Typ2 _ RFun.
  Variable Typ2Ok_arr : Typ2Ok Typ2_arr.
  Variable RSym_sym : RSym sym.
  Variable RSymOk_sym : RSymOk RSym_sym.

  Lemma lambda_exprD_typeof_not_None
  : forall tus tvs (e : expr typ sym) (t : typ) val,
      lambda_exprD tus tvs t e = Some val ->
      typeof_expr tus tvs e <> None.
  Proof.
    intros.
    generalize (lambda_exprD_typeof_expr _ (or_introl H)).
    congruence.
  Qed.

  Lemma lambda_exprD_typeof_Some
  : forall tus tvs e t val,
      lambda_exprD tus tvs t e = Some val ->
      typeof_expr tus tvs e = Some t.
  Proof.
    intros.
    generalize (lambda_exprD_typeof_expr _ (or_introl H)).
    congruence.
  Qed.

  Lemma lambda_exprD_typeof_eq
  : forall tus tvs e t t' val,
      lambda_exprD tus tvs t e = Some val ->
      typeof_expr tus tvs e = Some t' ->
      t = t'.
  Proof.
    intros.
    generalize (lambda_exprD_typeof_expr _ (or_introl H)).
    congruence.
  Qed.

  Global Instance Injective_typ2 {F : Type -> Type -> Type}
         {Typ2_F : Typ2 RType_typ F} {Typ2Ok_F : Typ2Ok Typ2_F} a b c d :
    Injective (typ2 a b = typ2 c d).
  refine {| result := a = c /\ b = d |}.
  abstract (
      eapply typ2_inj; eauto ).
  Defined.

  Global Instance Injective_typ1 {F : Type -> Type}
         {Typ1_F : Typ1 RType_typ F} {Typ2Ok_F : Typ1Ok Typ1_F} a b
  : Injective (typ1 a = typ1 b).
  refine {| result := a = b |}.
  abstract (
      eapply typ1_inj; eauto ).
  Defined.

  Lemma lambda_exprD_AppI tus tvs (t : typ) (e1 e2 : expr typ sym)
        (P : option (exprT tus tvs (typD t)) -> Prop)
        (H : exists u v1 v2, lambda_exprD tus tvs (typ2 u t) e1 = Some v1 /\
                             lambda_exprD tus tvs u e2 = Some v2 /\
                             P (Some (exprT_App v1 v2))) :
    P (lambda_exprD tus tvs t (App e1 e2)).
  Proof.
    autorewrite with exprD_rw; simpl.
    destruct H as [u [v1 [v2 [H1 [H2 HP]]]]].
    pose proof (lambda_exprD_typeof_Some _ _ H1).
    pose proof (lambda_exprD_typeof_Some _ _ H2).
    repeat (forward; inv_all; subst).
  Qed.

  Lemma lambda_exprD_InjI tus tvs (t : typ) (f : sym)
        (P : option (exprT tus tvs (typD t)) -> Prop)
        (H : exists v, symAs f t = Some v /\ P (Some (fun _ _ => v))) :
    P (lambda_exprD tus tvs t (Inj f)).
  Proof.
    autorewrite with exprD_rw; simpl.
    destruct (symAs f t); simpl; destruct H as [v [H1 H2]]; try intuition congruence.
    inv_all; subst. apply H2.
  Qed.

  Lemma lambda_exprD_beta tus tvs e t P
        (H : exists v, lambda_exprD tus tvs t e = Some v /\ P (Some v)) :
    P (lambda_exprD tus tvs t (beta e)).
  Proof.
    destruct H as [v [H1 H2]].
    pose proof (beta_sound tus tvs e t).
    forward; inv_all; subst.
    assert (v = e1).
    do 2 (apply functional_extensionality; intro).
    apply H3. subst. apply H2.
  Qed.

  Global Instance Injective_lambda_exprD_App tus tvs (e1 e2 : expr typ sym) (t : typ)
         (v : exprT tus tvs (typD t)):
    Injective (ExprDsimul.ExprDenote.lambda_exprD tus tvs t (App e1 e2) = Some v).
  Proof.
    refine {|
      result := exists u v1 v2, ExprDsimul.ExprDenote.lambda_exprD tus tvs (typ2 u t) e1 = Some v1 /\
                                ExprDsimul.ExprDenote.lambda_exprD tus tvs u e2 = Some v2 /\
                                v = exprT_App v1 v2;
      injection := fun H => _
    |}.
    autorewrite with exprD_rw in H.
    simpl in H. forward; inv_all; subst.
    do 3 eexists; repeat split; eassumption.
  Defined.

  Global Instance Injective_lambda_exprD_Inj tus tvs (f : sym) (t : typ) (v : exprT tus tvs (typD t)):
    Injective (ExprDsimul.ExprDenote.lambda_exprD tus tvs t (Inj f) = Some v).
  Proof.
    refine {|
      result := exists v', symAs f t = Some v' /\ v = fun _ _ => v';
      injection := fun H => _
    |}.
    autorewrite with exprD_rw in H.
    simpl in H. forward; inv_all; subst.
    eexists; repeat split.
  Defined.

  Lemma lambda_exprD_AppL : forall tus tvs tx ty f x fD,
      lambda_exprD tus tvs (typ2 (F:=RFun) tx ty) f = Some fD ->
      lambda_exprD tus tvs ty (App f x) =
      match lambda_exprD tus tvs tx x with
      | None => None
      | Some xD => Some (AbsAppI.exprT_App fD xD)
      end.
  Proof.
    simpl; intros.
    rewrite lambda_exprD_App.
    destruct (lambda_exprD tus tvs tx x) eqn:?.
    { erewrite lambda_exprD_typeof_Some by eassumption.
      rewrite H. rewrite Heqo. reflexivity. }
    { destruct (typeof_expr tus tvs x) eqn:?; auto.
      destruct (lambda_exprD tus tvs (typ2 t ty) f) eqn:?; auto.
      assert (t = tx).
      { destruct (ExprFacts.lambda_exprD_single_type H Heqo1).
        clear H0. eapply typ2_inj in x0; eauto.
        destruct x0. symmetry. apply H0. }
      { subst. rewrite Heqo. reflexivity. } }
  Qed.

  Lemma lambda_exprD_AppR : forall tus tvs tx ty f x xD,
      lambda_exprD tus tvs tx x = Some xD ->
      lambda_exprD tus tvs ty (App f x) =
      match lambda_exprD tus tvs (typ2 tx ty) f with
      | None => None
      | Some fD => Some (AbsAppI.exprT_App fD xD)
      end.
  Proof.
    simpl; intros.
    rewrite lambda_exprD_App.
    erewrite lambda_exprD_typeof_Some by eassumption.
    rewrite H.
    reflexivity.
  Qed.

  Lemma lambda_exprD_App_both_cases : forall tus tvs tx ty f x fD xD,
      lambda_exprD tus tvs (typ2 (F:=RFun) tx ty) f = Some fD ->
      lambda_exprD tus tvs tx x = Some xD ->
      lambda_exprD tus tvs ty (App f x) = Some (AbsAppI.exprT_App fD xD).
  Proof.
    intros. erewrite lambda_exprD_AppR by eassumption.
    rewrite H. reflexivity.
  Qed.

End some_lemmas.

Hint Rewrite lambda_exprD_App_both_cases using eassumption : exprD_rw.
Hint Rewrite lambda_exprD_AppL using eassumption : exprD_rw.
Hint Rewrite lambda_exprD_AppR using eassumption : exprD_rw.

Ltac red_exprD :=
  autorewrite with exprD_rw; simpl. (** TODO: this should be restricted **)

Ltac forward_exprD :=
  repeat match goal with
           | H : _ = _ , H' : _ = _ |- _ =>
             let x := constr:(@lambda_exprD_typeof_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H') in
             match type of x with
               | ?X = ?X => fail 1
               | _ => specialize x ; intro ; try inv_all ; try subst
             end
           | H : lambda_exprD _ _ ?T ?X = _ , H' : lambda_exprD _ _ ?T' ?X = _ |- _ =>
             match T with
               | T' => fail 1
               | _ =>
                 generalize (@lambda_exprD_deterministic _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H');
                   let X := fresh in intro X; red in X;
                   try inv_all; try subst
             end
         end.

Ltac arrow_case t :=
  let H := fresh in
  destruct (@typ2_match_case _ _ _ _ _ t) as [ [ ? [ ? [ ? H ] ] ] | H ];
    ( try rewrite H in * ).

Ltac arrow_case_any :=
  match goal with
    | H : context [ @typ2_match _ _ _ _ _ ?X ] |- _ =>
      arrow_case X
  end.

Section lemmas.
  Variable typ : Type.
  Variable RType_typ : RType typ.
  Variable RTypeOk : RTypeOk.

  Theorem Relim_const
  : forall T a b (pf : Rty a b),
      Relim (fun _ => T) pf = fun x => x.
  Proof.
    clear. destruct pf. reflexivity.
  Qed.

  Lemma type_cast_sym_Some
  : forall a b pf,
      type_cast a b = Some pf ->
      type_cast b a = Some (Rsym pf).
  Proof.
    intros. destruct pf.
    rewrite type_cast_refl; eauto.
  Qed.

  Lemma type_cast_sym_None
  : forall a b,
      type_cast a b = None ->
      type_cast b a = None.
  Proof.
    intros.
    destruct (type_cast b a); auto.
    destruct r.
    rewrite type_cast_refl in H; eauto.
  Qed.
End lemmas.
