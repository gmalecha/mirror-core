GENERIC := 
UTIL := Approx Iteration
PROVERS := ProverTac AssumptionProver
SUBST   := SealedSubst FastSubst RawSubst2 FMapSubst3
EXTENSIBLE := Types ExprCore \
	      ExprT \
	      ExprDI ExprDFacts ExprD3 ExprD \
	      ExprLift ExprUnifySyntactic ExprUnifySyntactic2 ExprUnifySyntactic3 \
	      ExprSubst LemmaExt \
	      Expr ExprTactics \
	      SetoidFold AppFull Red AsConst \
	      provers/UnifyEProver
LAMBDA := TypesI2 ResType \
	  ExprCore ExprDI ExprDsimul ExprD ExprDFacts \
	  ExprTac \
	  Expr ExprLift Red \
	  TypedFoldEager TypedFoldLazy TypedFoldApp \
	  WtExpr \
	  ExprUnify ExprUnify_simul \
	  ExprSubst AppN
LAMBDAM :=
POLY := Ctx Ctx2 TypeI ML ExprCore
STAC := Core Repeat Apply First Repeat Try STac
MODULES    := Generic \
	      TypesI EnvI ExprI ExprProp ExprSem \
	      SymI SymEnv SymPolyEnv \
	      SubstI SubstI2 SubstI3 \
	      Prover EProver Prover2 EProver2 \
	      Lemma LemmaApply \
	      $(EXTENSIBLE:%=Ext/%) \
	      $(LAMBDA:%=Lambda/%) \
	      $(LAMBDAM:%=LambdaM/%) \
	      $(PROVERS:%=provers/%) \
	      $(SUBST:%=Subst/%) \
	      $(UTIL:%=Util/%) \
	      $(STAC:%=STac/%)

# 	      $(POLY:%=Poly/%)

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
