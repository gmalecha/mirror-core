Require Import Omega.

Fixpoint lt_rem (a b : nat) : option nat :=
  match b with
    | 0 => Some a
    | S b' => match a with
                | 0 => None
                | S a' => lt_rem a' b'
              end
  end.

Lemma lt_rem_sound
: forall b a,
    match lt_rem a b with
      | None => a < b
      | Some c => a >= b /\ a - b = c
    end.
Proof.
  induction b; destruct a; simpl; intros; auto.
  { split; auto. red. omega. }
  { omega. }
  { specialize (IHb a).
    destruct (lt_rem a b); intuition. }
Qed.
