GENERIC := Iso IsoTac Approx
PROVERS := Assumption
#  Transitivity
EXTENSIBLE := Repr Types ExprCore \
	      ExprT ExprDI ExprD \
	      ExprFacts \
	      ExprLift ExprUnifySyntactic \
	      Expr
MODULES    := Generic \
	      TypesI EnvI ExprI ExprProp \
	      Prover Subst \
	      $(EXTENSIBLE:%=Ext/%)

TESTS :=
VS         := $(GENERIC:%=%.v) $(MODULES:%=%.v)
TVS        := $(TESTS:%=%.v)

ARGS :=-R . MirrorCore -R ../coq-ext-lib/theories ExtLib

.PHONY: coq clean package

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

install: coq
	$(MAKE) -f Makefile.coq install

Makefile.coq: Makefile $(VS)
	coq_makefile $(ARGS) $(VS) \
	  | sed -re 's/-R ([^ ]+) ExtLib/-I \1 -as ExtLib/g' \
          > Makefile.coq


Makefile.test.coq: Makefile $(TVS)
	coq_makefile $(ARGS) $(TVS) -o Makefile.test.coq

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

Ext/ExprD.v:
	(cd Ext; ln -s ExprD3.v ExprD.v)
