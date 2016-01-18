The Monoid Cancellation Demo
============================

This directory contains the implementation of a simple monoid cancellation
algorithm written completely in Rtac.

The implementation can be found in MonoidDemo.v. The algorithm proceeds in
three parts.

  1. [iter_left] permutes the left hand side of the equality,
     separating out each individual term. To produce a term somewhat
     like:
        P * ..1.. = ...

  2. [iter_right] permutes the right hand side of the equality,
     separating out individual terms. This leads a term like:
     	P * ..1.. = Q * ..2..

  3. At this point it applies a cancellation lemma which reduces the
     problem to prove
        P = Q            and       ..1.. = ..2..
     It invokes the [solver] tactic on the first equality and leaves
     the remainder of the goal to the rest of the algorithm.

In order to invoke the algorithm, a [cancel] tactic computes the size
of the terms and uses them to determine an appropriate amount of fuel
when invoking the above algorithm.

In the example, the [solver] tactic is simply applying reflexivity but
other choices are possible as well.


The implementation uses a reified language defined in any of the
MonoidSyntaxXxx files. These files implement the same language using
several choices.

- MonoidSyntaxSimple.v takes the simplest route to define a reified
  language. It uses the definition in MirrorCore.Simple

- MonoidSyntaxNoDec.v defines boolean equality decider functions and
  achieves a small performance improvement over the one that uses
  dependent types.

- MonoidSyntaxWithConst.v defines a special symbol for natural number
  constants and achieves approximately a factor of 3 performance
  improvement. It is important to note that in this case, natural
  number constants dominate the size of the problem which justifies
  the large performance improvemnt that we get by specializing their
  representation.

- MonoidSyntaxModular.v uses MirrorCore.ModularTypes to define the
  type language.
