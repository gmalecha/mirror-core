MONAD   := Expr Demo ReduceApprox Reduce ReduceWf
MONAD2  := MonadTypes MonadSym MonadExpr Tests MonadReify MonadReduce
MTAC    := Patterns McMatch
SETOID  := Demo
IMP     := Imp Wp
AUTO    := Demo
AUTORW  := Demo DemoQuantPull \
	   AutoRewriteLambda
CANCEL  := Lang LtacDemo CancelTac RtacDemo CancelTac2 RtacDemo2
# SetoidRewriteRec DemoSetoid
RTAC    := Demo
SIMPLE  := Simple SimpleReify SimpleExt FoldTest # SimpleRewrite
MODULES := $(MONAD2:%=Monad2/%) \
	   $(IMP:%=Imp/%) \
	   $(SIMPLE:%=Simple/%) \
	   $(CANCEL:%=Cancel/%) \
           $(AUTO:%=Auto/%) \
	   $(RTAC:%=RTac/%)

#	   $(AUTORW:%=AutoRewrite/%) \
# ExprDemo
#	      $(SETOID:%=setoid/%)
# 	      $(MTAC:%=mtac/%)
#	      $(MONAD:%=Monad/Monad%)

TESTS   :=
VS      := $(GENERIC:%=%.v) $(MODULES:%=%.v)
TVS     := $(TESTS:%=%.v)

ARGS :=-R . McExamples -R ../theories MirrorCore -I ../src

.PHONY: coq clean package

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

install: coq
	$(MAKE) -f Makefile.coq install

Makefile.coq: Makefile $(VS)
	coq_makefile -f _CoqProject -o Makefile.coq $(VS)

Makefile.test.coq: Makefile $(TVS)
	coq_makefile -f _CoqProject -o Makefile.test.coq $(TVS)

test: coq Makefile.test.coq
	$(MAKE) -f Makefile.test.coq

clean: Makefile.coq
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
