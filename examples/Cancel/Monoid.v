Module Type Monoid.
  Parameter M : Type.
  Parameter U : M.
  Parameter P : M -> M -> M.
  Parameter R : M -> M -> Prop.

  Local Infix "&" := P (at level 50).
  Local Infix "%is" := R (at level 70).

  Axiom plus_unit_p : forall b a, a %is b -> U & a %is b.
  Axiom plus_assoc_p1 : forall d c b a,
      a & (b & c) %is d -> (a & b) & c %is d.
  Axiom plus_assoc_p2 : forall d c b a,
      b & (a & c) %is d -> (a & b) & c %is d.
  Axiom plus_comm_p : forall c b a, a & b %is c -> b & a %is c.

  Axiom plus_unit_c : forall b a, a %is b -> a %is U & b.
  Axiom plus_assoc_c1 : forall d c b a,
      d %is a & (b & c) -> d %is (a & b) & c.
  Axiom plus_assoc_c2 : forall d c b a,
      d %is b & (a & c) -> d %is (a & b) & c.
  Axiom plus_comm_c : forall c b a, c %is a & b -> c %is b & a.
  Axiom plus_cancel : forall d c b a, a %is c -> b %is d -> a & b %is c & d.

  Axiom refl : forall a, a %is a.

End Monoid.