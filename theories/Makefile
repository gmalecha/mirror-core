GENERIC :=
UTIL := Approx Iteration
PROVERS := ProverTac AssumptionProver DefaultProver
SUBST   := UVarMap SealedSubst FMapSubst3 CascadeSubst # RawSubst2 FastSubst
EXTENSIBLE := Types ExprCore \
	      ExprT \
	      ExprDI ExprDFacts ExprD3 ExprD \
	      ExprLift ExprUnifySyntactic3 \
	      ExprSubst LemmaExt \
	      Expr ExprTactics \
	      SetoidFold AppFull Red AsConst \
	      provers/UnifyEProver
# ExprUnifySyntactic ExprUnifySyntactic2
LAMBDA := ResType \
	  ExprCore ExprDI ExprDsimul ExprD ExprDFacts \
	  ExprTac \
	  Expr ExprLift Red \
	  TypedFoldEager TypedFoldLazy TypedFoldApp FoldApp \
	  WtExpr \
	  ExprUnify ExprUnify_simul ExprUnifyHO \
	  ExprSubst AppN
LAMBDAM := ExprCore ExprCore_simul
POLY := Ctx Ctx2 TypeI ML ExprCore
STAC := Core Repeat Apply First Repeat Try Idtac Rec Simplify STac
SYMS := SymEnv SymPolyEnv SymSum
MODULES    := Generic \
	      TypesI EnvI ExprI ExprProp ExprSem \
	      SymI \
	      SubstI SubstI3 \
	      Prover EProver Prover2 EProver2 \
	      Lemma LemmaApply \
	      $(POLY:%=Poly/%) \
	      $(LAMBDA:%=Lambda/%) \
	      $(LAMBDAM:%=LambdaM/%) \
	      $(SUBST:%=Subst/%) \
	      $(UTIL:%=Util/%) \
	      $(STAC:%=STac/%) \
	      $(SYMS:%=syms/%) \
	      $(PROVERS:%=provers/%)

#	      $(EXTENSIBLE:%=Ext/%)

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
