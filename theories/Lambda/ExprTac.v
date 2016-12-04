Require Import Coq.Logic.FunctionalExtensionality.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.Compat.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.AbsAppI.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprD.
Require Import MirrorCore.Lambda.ExprDFacts.
Require Import MirrorCore.Lambda.Red.

Set Implicit Arguments.
Set Strict Implicit.

Section some_lemmas.
  Variable typ : Set.
  Variable sym : Set.
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
    Injective (typ2 a b = typ2 c d) :=
  { result := a = c /\ b = d }.
  abstract (
      eapply typ2_inj; eauto ).
  Defined.

  Global Instance Injective_typ1 {F : Type -> Type}
         {Typ1_F : Typ1 RType_typ F} {Typ2Ok_F : Typ1Ok Typ1_F} a b
  : Injective (typ1 a = typ1 b) :=
  { result := a = b }.
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
    Injective (ExprDsimul.ExprDenote.lambda_exprD tus tvs t (App e1 e2) = Some v) := {
      result := exists u v1 v2, ExprDsimul.ExprDenote.lambda_exprD tus tvs (typ2 u t) e1 = Some v1 /\
                                ExprDsimul.ExprDenote.lambda_exprD tus tvs u e2 = Some v2 /\
                                v = exprT_App v1 v2;
      injection := fun H => _
    }.
  Proof.
    autorewrite with exprD_rw in H.
    simpl in H. forward; inv_all; subst.
    do 3 eexists; repeat split; eassumption.
  Defined.

  Global Instance Injective_lambda_exprD_Inj tus tvs (f : sym) (t : typ) (v : exprT tus tvs (typD t)):
    Injective (ExprDsimul.ExprDenote.lambda_exprD tus tvs t (Inj f) = Some v) := {
      result := exists v', symAs f t = Some v' /\ v = exprT_Inj _ _ v';
      injection := fun H => _
    }.
  Proof.
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

  Lemma lambda_exprD_App
    : forall tus tvs td tr f x fD xD,
      lambda_exprD tus tvs (typ2 (F:=RFun) td tr) f = Some fD ->
      lambda_exprD tus tvs td x = Some xD ->
      lambda_exprD tus tvs tr (App f x) = Some (AbsAppI.exprT_App fD xD).
  Proof using Typ2Ok_arr RSymOk_sym RTypeOk.
    intros.
    autorewrite with exprD_rw; simpl.
    erewrite lambda_exprD_typeof_Some by eauto.
    rewrite H. rewrite H0. reflexivity.
  Qed.

  Lemma lambda_exprD_Abs_prem
    : forall tus tvs t t' x xD,
      ExprDsimul.ExprDenote.lambda_exprD tus tvs t (Abs t' x) = Some xD ->
      exists t'' (pf : typ2 t' t'' = t) bD,
        ExprDsimul.ExprDenote.lambda_exprD tus (t' :: tvs) t'' x = Some bD /\
        xD = match pf with
             | eq_refl => AbsAppI.exprT_Abs bD
             end.
  Proof using Typ2Ok_arr RSymOk_sym RTypeOk.
    intros.
    autorewrite with exprD_rw in H.
    destruct (typ2_match_case t); forward_reason.
    { rewrite H0 in H; clear H0.
      red in x2; subst. simpl in *.
      autorewrite_with_eq_rw_in H.
      destruct (type_cast x0 t'); subst; try congruence.
      red in r; subst.
      forward. inv_all; subst.
      eexists; exists eq_refl.
      eexists; split; eauto. inversion H.
      unfold AbsAppI.exprT_Abs.
      autorewrite_with_eq_rw.
      reflexivity. }
    { rewrite H0 in H. congruence. }
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
  Variable typ : Set.
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

(** TODO: This needs to move *)
Section thing.
  Variable typ : Set.
  Variable RType_typ : RType typ.
  Variable RTypeOk_typ : RTypeOk.
  Variable F : Type@{Urefl} -> Type@{Urefl} -> Type@{Urefl}.
  Variable Typ2_F : Typ2 _ F.
  Variable Typ2Ok_F : Typ2Ok Typ2_F.


  Definition typ2_Rty (a b c d : typ) (pf : Rty a b) (pf' : Rty c d)
  : Rty (typ2 a c) (typ2 b d) :=
    match pf , pf' with
    | eq_refl , eq_refl => eq_refl
    end.

  Lemma decompose_Rty_typ2 : forall {a b c d : typ} (pf : Rty (typ2  a b) (typ2 c d)),
      exists pf' pf'', pf = typ2_Rty pf' pf''.
  Proof.
    intros. generalize pf.
    intros. inv_all.
    subst. exists eq_refl. exists eq_refl. simpl.
    apply UIP_refl.
  Defined.

  Lemma symAs_D :
    forall (Typ2_Fun : Typ2 RType_typ RFun)
      (func : Set) (RSym_func : RSym func),
      forall (f : func) (t : typ) (v : typD t),
        symAs f t = Some v ->
        match typeof_sym f as X return match X with
                                       | None => unit
                                       | Some t => typD t
                                       end -> Prop with
        | None => fun _ => False
        | Some t' => fun d =>
                      exists pf : Rty t' t,
                        Rcast_val pf d = v
        end (symD f).
  Proof.
    clear. intros.
    unfold symAs in H.
    generalize dependent (symD f).
    destruct (typeof_sym f).
    { intros. destruct (type_cast t t0).
      { exists (Rsym r). inv_all. unfold Rcast_val, Rcast, Relim in *.
        unfold Rsym. rewrite eq_sym_involutive. assumption. }
      { exfalso. clear - H. discriminate H. } }
    { clear. intros. discriminate H. }
  Defined.

  Lemma Rcast_val_eq_refl : forall a pf x, @Rcast_val _ _ a a pf x = x.
  Proof.
    intros. rewrite (UIP_refl pf). reflexivity.
  Defined.



End thing.


Ltac lambda_exprD_fwd :=
  repeat match goal with
         | H : symAs _ _ = Some _ |- _ =>
           (eapply symAs_D in H; eauto); [] ; simpl in H; destruct H
         | pf : Rty _ _ |- _ =>
           destruct (decompose_Rty_typ2 _ _ pf) as [ ? [ ? ? ] ] ; subst pf
         | pf : lambda_exprD _ _ _ (Abs _ _) = Some _ |- _ =>
           apply lambda_exprD_Abs_prem in pf ; eauto ; [ ] ; destruct pf as [ ? [ ? [ ? [ ? ? ] ] ] ]
         | pf : Rty _ ?X |- _ => is_var X ; destruct pf
         | pf : Rty ?X _ |- _ => is_var X ; red in pf ; subst X
         | |- _ => progress inv_all ; subst
         end.

Require Import MirrorCore.ExprI.
Section exprT.
  Context {typ : Set}.
  Context {RType_typ : RType typ}.
  (** TODO(gmalecha): These should go somewhere else since they are generic
   ** to exprT.
   **)
  Lemma exprT_Inj_castR
  : forall (tus tvs : tenv typ) (T : Type@{Urefl}) (Ty0 : Typ0 _ T) (v : T),
    @exprT_Inj _ _ _ _ (typD _) (castR (@id Type@{Urefl}) T v) = castR (exprT tus tvs) _ (exprT_Inj _ _ v).
  Proof.
    clear. unfold exprT_Inj, castR. intros.
    generalize dependent (typ0_cast (F:=T)).
    intro e. generalize dependent (typD (typ0 (F:=T))).
    intros; subst. reflexivity.
  Defined.

  Theorem exprT_App_castRl
    : forall (tus tvs : tenv typ) (T U : Type@{Urefl})
        (Ty2 : Typ2 _ RFun) (Ty0T : Typ0 _ T) (Ty0U : Typ0 _ U)
        e1 e2,
      AbsAppI.exprT_App (castR (exprT tus tvs) (RFun T U) e1) e2 =
      castR (exprT tus tvs) U (Applicative.ap e1 (castD (exprT tus tvs) T e2)).
  Proof.
    unfold AbsAppI.exprT_App, castR, castD. simpl; intros.
    generalize dependent (typ0_cast (F:=U)).
    generalize dependent (typ0_cast (F:=T)).
    generalize dependent (typ2_cast (typ0 (F:=T)) (typ0 (F:=U))).
    clear.
    intros.
    generalize dependent (typD (typ0 (F:=T))).
    generalize dependent (typD (typ0 (F:=U))).
    intros; subst. simpl.
    generalize dependent (typD (typ2 (typ0 (F:=T)) (typ0 (F:=U)))).
    intros; subst. reflexivity.
  Defined.
End exprT.

Ltac simpl_exprT :=
  repeat match goal with
         | |- context [ (fun a b => ?F a b) ] =>
           change (fun a b => F a b) with F
         | |- _ => rewrite castDR
         | |- _ => rewrite castRD
         | |- context [ exprT_Inj ?tus ?tvs (@castR _ _ _ _ ?T ?v) ] =>
           let H := fresh in
           pose proof (@exprT_Inj_castR _ _ tus tvs _ T v) as H ; change_rewrite H ; clear H
         | |- context [ @AbsAppI.exprT_App _ _ _ ?tus ?tvs ?d ?c (@castR _ _ _ ?T _ ?f) ?x] =>
           let H := fresh in
           pose proof (@exprT_App_castRl _ _ tus tvs _ _ _ _ _ f x) as H ; change_rewrite H ; clear H
         end.



(* TODO(gmalecha): Remove this. It appears to be duplicated.
Section ExprDInject.
  Context {typ func : Set}.
  Context {RType_typ : RType typ} {RTypeOk_typ : RTypeOk}.
  Context {RSym_func : RSym func} {RSymOk_func : RSymOk RSym_func}.
  Context {Typ2_tyArr : Typ2 _ RFun} {Typ2Ok_tyArr : Typ2Ok Typ2_tyArr}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ Typ2_tyArr.

  Global Instance Injective_lambda_exprD_App tus tvs (e1 e2 : expr typ func) (t : typ)
         (v : exprT tus tvs (typD t)):
    Injective (ExprDsimul.ExprDenote.lambda_exprD tus tvs t (App e1 e2) = Some v) := {
      result := exists u v1 v2, ExprDsimul.ExprDenote.lambda_exprD tus tvs (tyArr u t) e1 = Some v1 /\
                                ExprDsimul.ExprDenote.lambda_exprD tus tvs u e2 = Some v2 /\
                                v = AbsAppI.exprT_App v1 v2;
      injection := fun H => _
    }.
  Proof.
    autorewrite with exprD_rw in H.
    simpl in H. forward; inv_all; subst.
    do 3 eexists; repeat split; eassumption.
  Defined.

  Global Instance Injective_lambda_exprD_Inj tus tvs (f : func) (t : typ) (v : exprT tus tvs (typD t)):
    Injective (ExprDsimul.ExprDenote.lambda_exprD tus tvs t (Inj f) = Some v) := {
      result := exists v', symAs f t = Some v' /\ v = exprT_Inj _ _ v' ;
      injection := fun H => _
    }.
  Proof.
    autorewrite with exprD_rw in H.
    simpl in H. forward; inv_all; subst.
    eexists; repeat split.
  Defined.

End ExprDInject.
*)