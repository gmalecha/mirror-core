Require Import MirrorCore.Reify.Patterns.

Class Reify (T : Type) : Type :=
{ reify_scheme : Command T }.

Arguments reify_scheme _ {_}.

Export MirrorCore.Reify.Patterns.
