Parameter M : Type.
Parameter U : M.
Parameter P : M -> M -> M.
Parameter R : M -> M -> Prop.
Parameter N : nat -> M.

Local Infix "&" := P (at level 50).
Local Infix "%is" := R (at level 70).

Axiom plus_unit_p : forall a b, a %is b -> U & a %is b.
Axiom plus_assoc_p1 : forall a b c d,
    a & (b & c) %is d -> (a & b) & c %is d.
Axiom plus_assoc_p2 : forall a b c d,
    b & (a & c) %is d -> (a & b) & c %is d.
Axiom plus_comm_p : forall a b c, a & b %is c -> b & a %is c.

Axiom plus_unit_c : forall a b, a %is b -> a %is U & b.
Axiom plus_assoc_c1 : forall a b c d,
    d %is a & (b & c) -> d %is (a & b) & c.
Axiom plus_assoc_c2 : forall a b c d,
    d %is b & (a & c) -> d %is (a & b) & c.
Axiom plus_comm_c : forall a b c, c %is a & b -> c %is b & a.
Axiom plus_cancel : forall a b c d, a %is c -> b %is d -> a & b %is c & d.

Axiom refl : forall a, a %is a.

Fixpoint build_plusL n : M :=
  match n with
    | 0 => N 0
    | S n' => N n & (build_plusL n')
  end.

Fixpoint build_plusR n : M :=
  match n with
    | 0 => N 0
    | S n' => (build_plusR n') & N n
  end.

Definition goal n := (build_plusL n) %is (build_plusR n).

Ltac prep := unfold goal, build_plusL, build_plusR.