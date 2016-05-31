Require PluginUtils.PluginUtils.
Require Import MirrorCore.Reify.Patterns.
Require MirrorCore.Lemma.

Declare ML Module "reify_Lambda_plugin".

Export MirrorCore.Reify.Patterns.

Class Reify (T : Type) : Type :=
  reify_scheme : Command T.