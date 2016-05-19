mirror-core
===========

MirrorCore is a library for extensible reflective automation. It includes two
main components.

- Lambda -- a simply typed lambda calculus to use as the reflective core
  language
- RTac -- a reflective tactic language modeled on Ltac.

The system is described at a mathematical level in two works:

- [Extensible Proof Engineering in Intensional Type Theory](https://gmalecha.github.io/publications/extensible-proof-engineering-in-intensional-type-theory.html) by Gregory Malecha (PhD Dissertation)
- [Extensible and Efficient Automation through Reflective Tactics](http://gmalecha.github.io/publication/2016/01/01/extensible-and-efficient-automation-through-reflective-tactics/) by Gregory Malecha & Jesper Bengtson (ESOP'16)

Bugs
----

If you find a bug, please report it on github: https://github.com/gmalecha/mirror-core/issues

Install with OPAM
-----------------
Add the Coq repository:

    opam repo add coq-released https://coq.inria.fr/opam/released

and run:

    opam install coq-mirror-core

To get the beta versions of Coq, activate the repository:

    opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev


Quick Start
-----------

This version of MirrorCore builds on Coq 8.5.

(In the following commands 'mirror-core' refers to the root directory
of mirror-core)

(If you need to set up dependencies, please see the next section first)

To build the library, run:

```
mirror-core/ $ make -jN
```

in the main directory.

You can build the examples by running

```
mirror-core/examples/ $ make -jN
```

in the examples directory.

Dependencies
------------

MirrorCore depends on two external libraries.

- [coq-ext-lib](https://github.com/coq-ext-lib/coq-ext-lib)
- [coq-plugin-utils](https://github.com/gmalecha/coq-plugin-utils) (to build the plugins)

Both of these can be installed using opam,
provided you have added the repository described above.

```
opam install coq-ext-lib coq-plugin-utils
```

coq-plugin-utils needs to be installed, you should follow the
directions in the README.md in that repository.

coq-ext-lib does not need to be installed.

If you do install it, simply touch coq-ext-lib in the mirror-core
folder to prevent pulling a fresh copy.

```
mirror-core/ $ touch coq-ext-lib
```

If you already have a copy of coq-ext-lib on your system but it is not
installed, you can create a symbolic link to it in the mirror-core
directory.

```
ln -s <path/to/coq-ext-lib> coq-ext-lib
```

If you do not have a local copy already you can run

```
mirror-core/ $ make init
```

which will pull a fresh copy of coq-ext-lib and build it.

In order to build the reification plugin, you must use OCaml 4.01 or later.
