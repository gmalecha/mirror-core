Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.ExprCore.

Set Implicit Arguments.
Set Strict Implicit.

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