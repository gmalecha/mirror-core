Require Import RelationClasses.
Require Import ExtLib.Data.Positive.

Set Implicit Arguments.
Set Strict Implicit.

Section approx.
  Variable T : Type.
  Variable f : (T -> T * bool) -> T -> T * bool.

  Fixpoint approx (x : T) (fuel : nat) : T * bool :=
    match fuel with
      | 0 => (x,false)
      | S fuel =>
        f (fun z => approx z fuel) x
    end.

  Section relational.
    Variable P : T -> T -> Prop.
    Hypothesis Refl_P : Reflexive P.
    Hypothesis Trans_P : Transitive P.
    Hypothesis related : forall F, (forall y, P y (fst (F y))) -> forall x, P x (fst (f F x)).

    Theorem approx_preserves : forall n x,
                                   P x (fst (approx x n)).
    Proof.
      induction n; simpl; intros; auto.
    Qed.
  End relational.

End approx.

Section approx2.
  Variable T : Type.
  Variable stop : T -> T -> bool.
  Variable f : T -> T.

  Definition approx2 (x : T) (fuel : nat) : T :=
    fst (approx (fun F x => let x' := f x in
                            if stop x x' then (x,false) else F x') x fuel).

  Variable P : T -> Prop.
  Hypothesis preserves : forall x, P x -> P (f x).

  Lemma approx2_preserves : forall n x,
                              P x ->
                              P (approx2 x n).
  Proof.
    unfold approx2.
    intros. revert H. eapply approx_preserves; auto; intros.
    destruct (stop x0 (f x0)); simpl; auto.
  Qed.
End approx2.
