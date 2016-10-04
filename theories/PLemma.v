Require Import MirrorCore.Lemma.
Require Import MirrorCore.Polymorphic.

Section PolyLemma.
  Context {typ expr conclusion : Type}.

  Record PolyLemma := {
    p_n : nat;                    
    p_lem : polymorphic typ p_n (lemma typ expr conclusion);
    p_tc : polymorphic typ p_n bool
  }.

End PolyLemma.

Arguments PolyLemma : clear implicits.
