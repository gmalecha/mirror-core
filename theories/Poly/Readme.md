Poly Language
=============

This language implements a two-universe polymorphic language based on the
type system of System Fw. The structure is the following:

(Large Kinds) k1 ::= U1

(Small Kinds) k0 ::= U0 | k0 -> k0

(Large Types) t1 ::= Pi k0 . t1 | (t0)

(Small Types) t0 ::= T | t0 -> t0 | t0 t0 | x

(Expressions) e  ::= e e | \ t0 . e | x | E | e t0
