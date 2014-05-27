MONAD   := Expr Demo ReduceApprox Reduce ReduceWf
MONAD2  := MonadTypes MonadSym MonadExpr Tests
MTAC    := Patterns McMatch
SETOID  := Demo
AUTO    := AutoProver AutoProver2 # Demo Demo2 -- temporary
AUTORW  := SetoidRewrite
MODULES := ExprDemo \
	      $(MONAD:%=Monad/Monad%) \
	      $(MONAD2:%=Monad2/%) \
	      $(MTAC:%=mtac/%) \
	      $(SETOID:%=setoid/%) \
	      $(AUTO:%=Auto/%) \
	      $(AUTORW:%=AutoRewrite/%)
TESTS   :=
VS      := $(GENERIC:%=%.v) $(MODULES:%=%.v)
TVS     := $(TESTS:%=%.v)

ARGS :=-R . MirrorCore.Examples -R ../theories MirrorCore

.PHONY: coq clean package

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

install: coq
	$(MAKE) -f Makefile.coq install

Makefile.coq: Makefile $(VS)
	coq_makefile $(ARGS) $(VS) > Makefile.coq

Makefile.test.coq: Makefile $(TVS)
	coq_makefile $(ARGS) $(TVS) > Makefile.test.coq

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

-include ../Makefile.paths
