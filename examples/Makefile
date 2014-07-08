MONAD   := Expr Demo ReduceApprox Reduce ReduceWf
MONAD2  := MonadTypes MonadSym MonadExpr Tests MonadReify MonadReduce
MTAC    := Patterns McMatch
SETOID  := Demo
IMP     := Imp Wp
AUTO    := AutoProver # Demo Demo2 -- temporary
AUTORW  := SetoidRewrite AutoRewriteLambda
SIMPLE  := Simple
MODULES := $(MONAD2:%=Monad2/%) \
	   $(IMP:%=Imp/%) \
	   $(SIMPLE:%=Simple/%) \
           $(AUTO:%=Auto/%)

# ExprDemo
#	      $(SETOID:%=setoid/%)
# 	      $(MTAC:%=mtac/%)
# 	      $(AUTORW:%=AutoRewrite/%)
#	      $(MONAD:%=Monad/Monad%)

TESTS   :=
VS      := $(GENERIC:%=%.v) $(MODULES:%=%.v)
TVS     := $(TESTS:%=%.v)

ARGS :=-R . McExamples -R ../theories MirrorCore

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
