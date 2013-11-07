MONAD := Expr Demo ReduceApprox Reduce ReduceWf
SEPLOG := NatDed SepLog SepHeap
MTAC := Patterns McMatch
MODULES    := ExprDemo \
	      $(MONAD:%=Monad/Monad%) \
	      $(SEPLOG:%=SepLog/%) \
	      $(MTAC:%=mtac/%)
TESTS :=
VS         := $(GENERIC:%=%.v) $(MODULES:%=%.v)
TVS        := $(TESTS:%=%.v)

ARGS :=-R . Examples -R ../src MirrorCore -R ../coq-ext-lib/theories ExtLib

.PHONY: coq clean package

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

install: coq
	$(MAKE) -f Makefile.coq install

Makefile.coq: Makefile $(VS)
	coq_makefile $(ARGS) $(VS) \
	  | sed -re 's/-R ([^ ]+) ExtLib/-I \1 -as ExtLib/g' \
	  | sed -re 's/-R ([^ ]+) MirrorCore/-I \1 -as MirrorCore/g' \
	  > Makefile.coq

Makefile.test.coq: Makefile $(TVS)
	coq_makefile $(ARGS) $(TVS) \
	  | sed -re 's/-R ([^ ]+) ExtLib/-I \1 -as ExtLib/g' \
	  | sed -re 's/-R ([^ ]+) MirrorCore/-I \1 -as MirrorCore/g' \
	  > Makefile.test.coq

test: coq Makefile.test.coq
	$(MAKE) -f Makefile.test.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.test.coq .depend

package:
	hg archive -t tgz /tmp/mirror-core.tgz

admit:
	@ grep -n -e 'admit' -e 'Admitted' ${VS}

depgraph: Makefile.coq
	@ echo Generating dependency graph to ../deps.pdf
	@ ./../tools/deps.py $(MODULES:%=%.v.d) > ../deps.dot
	@ ./../tools/deps.py $(MODULES:%=%.v.d) | dot -Tpdf -o ../deps.pdf

toplevel: coq
	coqtop.opt $(ARGS)
