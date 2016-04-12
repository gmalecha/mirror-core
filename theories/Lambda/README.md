The Lambda Core Language
========================

This directory provides a core lambda-calculus augmented with base
constants and unification variabls. It is parametrized over an
arbitrary type language which must contain a representation of
function types (as a Typ2).

Abstracting the type system makes it possible to represent types and
terms that require features not supported by simple types,
e.g. polymorphism and some forms of dependent types.

To build on the lambda language, you can import the core definitions
using the following code.

```
Require Import MirrorCore.Lambda.Expr.
```

This will give you access to the the core syntax (defined in
[[ExprCore.v]]), and the instances of ```Expr``` and ```ExprOk``` that
are necessary to use the rest of MirrorCore.

Unification
-----------

There are two unification algorithms implemented for Lambda. The
default, ExprUnify_simul simultaneously performs type inference and
unification. A simpler, less-efficient, implementation lives in
ExprUnify_simple.

Reduction
---------

Reduction is implemented in two files:

- [[Red.v]] implements head beta reduction

- [[RedAll.v]] implements full term reduction, including reduction
  under binders. It is *not* currently complete, i.e. reducing a term
  is *not* an idempotent operation, though it could be made one.

Patterns
--------

The deep patterns are implemented in [[Ptrns.v]].

Setoid Rewriting
----------------

In addition to the core language,
```MirrorCore.Lambda.AutoSetoidRewriteRtac``` provides an
implementation of a setoid rewriting engine that exports an Rtac
interface.

The examples directory contains the following example:

- [[examples/AutoRewrite/DemoQuantPullRtac.v]] implements quantifier
  pulling.


Relations are represented by the ```Rbase``` parameter of the tactic
to allow clients to choose convenient instantiations. A generic choice
is to re-use ```expr``` as the type of relations; however, note that
the denotation function for expressions does *not* get access to local
variables.

The primary entry point is ```auto_setoid_rewrite_bu```
which is parameterized by decision procedures for determining whether
gi