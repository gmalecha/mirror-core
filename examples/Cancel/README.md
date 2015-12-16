The Monoid Cancellation Demo
============================

This directory contains the implementation of a simple monoid cancellation
algorithm written completely in Rtac.

The basic implementation can be found in MonoidDemo.v. This file uses
basic definitions and achieves reasonable performance on large
problems.

The other two files show various optimizations to the representation
that yield performance benefits.

- MonoidDemoNoDec.v defines boolean equality decider functions and
  achieves a small performance improvement.

- MonoidDemoWithConst.v defines a special symbol for natural number
  constants and achieves approximately a factor of 3 performance
  improvement. It is important to note that in this case, natural
  number constants dominate the size of the problem which justifies
  the large performance improvemnt that we get by specializing their
  representation.