Require Import MirrorCore.Reify.Patterns.

Polymorphic Class Reify@{U} (T : Type@{U}) : Prop :=
{ reify_scheme : Command@{U} T }.

Arguments reify_scheme _ {_}.

Export MirrorCore.Reify.Patterns.
