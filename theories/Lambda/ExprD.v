Require Import Coq.Bool.Bool.
Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.VariablesI.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprDFacts.
Require MirrorCore.Lambda.ExprDsimul.

Require Import FunctionalExtensionality.

Set Implicit Arguments.
Set Strict Implicit.

Export ExprDsimul.ExprDenote.

Module ExprFacts := ExprDFacts.Make ExprDsimul.ExprDenote.

Export MirrorCore.Lambda.ExprCore.
Export MirrorCore.SymI.
