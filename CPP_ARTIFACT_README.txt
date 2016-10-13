Here is the Artifact for our CPP 2017 submission.
To build this development, follow the instructions in README.md in this directory. We built this using Coq v. 8.5pl1 on Linux.

Here's a list of the most important content of the artifact relevant to the paper:

examples/Tauto: tautology-solve case study
examples/PolyRewrite/QuantifierPuller: quantifier-puller case study
examples/PolyRewrite/Monads: monad normalization case study

examples/Cancel/MonoidSyntaxModular: cancellation example

theories/CTypes: core-types abstraction
theories/Polymorphic.v: extensional embedding of polymorphism
theories/Lambda/PolyInst.v: polymorphic instantiation
theories/Lambda/Rewrite/Respectful.v: polymorphic respectfulness hints
theories/Lambda/Rewrite/HintDbs.v: polymorphic rewriting hint databases
theories/RTac/PApply.v: polymorphic apply tactic
