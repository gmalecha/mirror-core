GENERIC := Iso IsoTac Approx
PROVERS := ProverTac AssumptionProver
SUBST   := SealedSubst FastSubst RawSubst2
EXTENSIBLE := Repr Types ExprCore \
	      ExprT \
	      ExprDI ExprDFacts ExprD3 ExprD \
	      ExprLift ExprUnifySyntactic ExprUnifySyntactic2 ExprUnifySyntactic3 \
	      ExprSubst LemmaExt \
	      Expr ExprTactics \
	      SymEnv \
	      SetoidFold AppFull Red AsConst \
	      provers/UnifyEProver
LAMBDA := ExprCore ExprT ExprDI ExprD3
MODULES    := Generic \
	      TypesI EnvI ExprI ExprProp ExprSem \
	      SymI \
	      SubstI SubstI2 SubstI3 \
	      Prover EProver EProver2 EProver3 \
	      $(EXTENSIBLE:%=Ext/%) \
	      $(LAMBDA:%=Lambda/%) \
	      $(PROVERS:%=provers/%) \
	      $(SUBST:%=Subst/%)


TESTS :=
VS         := $(GENERIC:%=%.v) $(MODULES:%=%.v)
TVS        := $(TESTS:%=%.v)

ARGS := -R . MirrorCore

.PHONY: coq clean package

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

install: coq
	$(MAKE) -f Makefile.coq install

Makefile.coq: Makefile $(VS)
	echo $(ARGS)
	coq_makefile $(ARGS) $(VS) > Makefile.coq


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

-include ../Makefile.paths
