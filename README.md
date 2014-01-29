mirror-core
===========

A framework for general, extensible, reflective decision procedures. 

Bugs
----

If you find a bug, please report it.

Quick Start
-----------

(In the following commands 'mirror-core' refers to the root directory of mirror-core)

To pull in read-only copies of all of the dependencies, run the following:

```
mirror-core/ $ make -jN init
```

where N is the maximum number of coqc processes that you would like to run simultaneously.

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

If you use emacs & proof-general, then you may find it convenient to run

```
mirror-core/ $ make .dir-locals.el
```

which will set up the -R and -I options to pass to coqtop from proof general (this is directory local only and relies on absolute paths, so if you move the installation, you will need to run this again).

Dependencies
------------

- coq-ext-lib (https://github.com/coq-ext-lib/coq-ext-lib)
