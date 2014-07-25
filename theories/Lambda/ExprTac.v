Require Import ExtLib.Tactics.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprD.
Require Import MirrorCore.Lambda.ExprDFacts.

Set Implicit Arguments.
Set Strict Implicit.

Section some_lemmas.
  Variable typ : Type.
  Variable sym : Type.
  Variable RType_typ : RType typ.
  Variable RTypeOk : RTypeOk.
  Variable Typ2_arr : Typ2 _ Fun.
  Variable Typ2Ok_arr : Typ2Ok Typ2_arr.
  Variable RSym_sym : RSym sym.
  Variable RSymOk_sym : RSymOk RSym_sym.

  Lemma exprD_typeof_not_None
  : forall ts tus tvs e t val,
      exprD' ts tus tvs t e = Some val ->
      typeof_expr ts tus tvs e <> None.
  Proof.
    intros.
    generalize (exprD'_typeof_expr _ (or_introl H)).
    congruence.
  Qed.

  Lemma exprD_typeof_Some
  : forall ts tus tvs e t val,
      exprD' ts tus tvs t e = Some val ->
      typeof_expr ts tus tvs e = Some t.
  Proof.
    intros.
    generalize (exprD'_typeof_expr _ (or_introl H)).
    congruence.
  Qed.

  Lemma exprD_typeof_eq
  : forall ts tus tvs e t t' val,
      exprD' ts tus tvs t e = Some val ->
      typeof_expr ts tus tvs e = Some t' ->
      t = t'.
  Proof.
    intros.
    generalize (exprD'_typeof_expr _ (or_introl H)).
    congruence.
  Qed.

  Global Instance Injective_typ2 a b c d : Injective (typ2 a b = typ2 c d) :=
  { result := a = c /\ b = d }.
  abstract (
      eapply typ2_inj with (ts := nil); eauto ).
  Defined.

End some_lemmas.

Ltac red_exprD :=
  autorewrite with exprD_rw; simpl. (** TODO: this should be restricted **)

Ltac forward_exprD :=
  repeat match goal with
           | H : _ = _ , H' : _ = _ |- _ =>
             let x := constr:(@exprD_typeof_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H') in
             match type of x with
               | ?X = ?X => fail 1
               | _ => specialize x ; intro ; try inv_all ; try subst
             end
           | H : exprD' _ _ _ ?T ?X = _ , H' : exprD' _ _ _ ?T' ?X = _ |- _ =>
             match T with
               | T' => fail 1
               | _ =>
                 generalize (@exprD'_deterministic _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H');
                   let X := fresh in intro X; red in X;
                   try inv_all; try subst
             end
         end.

Ltac arrow_case ts t :=
  let H := fresh in
  destruct (@typ2_match_case _ _ _ _ _ ts t) as [ [ ? [ ? [ ? H ] ] ] | H ];
    ( try rewrite H in * ).

Section lemmas.
  Variable typ : Type.
  Variable RType_typ : RType typ.
  Variable RTypeOk : RTypeOk.

  Theorem Relim_const
  : forall T ts a b (pf : Rty ts a b),
      Relim (fun _ => T) pf = fun x => x.
  Proof.
    clear. destruct pf. reflexivity.
  Qed.

  Lemma type_cast_sym_Some
  : forall ts a b pf,
      type_cast ts a b = Some pf ->
      type_cast ts b a = Some (Rsym pf).
  Proof.
    intros. destruct pf.
    rewrite type_cast_refl; eauto.
  Qed.

  Lemma type_cast_sym_None
  : forall ts a b,
      type_cast ts a b = None ->
      type_cast ts b a = None.
  Proof.
    intros.
    destruct (type_cast ts b a); auto.
    destruct r.
    rewrite type_cast_refl in H; eauto.
  Qed.
End lemmas.