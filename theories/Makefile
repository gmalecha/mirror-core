GENERIC :=
UTIL := Approx Iteration ListMapT Forwardy
PROVERS := ProverTac AssumptionProver DefaultProver AutoProver
SUBST   := UVarMap FMapSubst CascadeSubst # SealedSubst RawSubst2 FastSubst
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
	  Expr ExprLift Red RedAll \
	  TypedFoldEager TypedFoldLazy TypedFoldApp FoldApp StrongFoldApp \
	  WtExpr \
	  ExprUnify_common ExprUnify ExprUnify_simul \
	  ExprSubst AppN
# ExprUnifyHO
LAMBDAM := ExprCore ExprCore_simul
POLY := Ctx Ctx2 TypeI ML ExprCore
STAC := Core Repeat Apply EApply First Repeat Try Idtac Rec Simplify Solve Then Fail Continuation UseForAll STac
SYMS := SymEnv SymPolyEnv SymSum
MODULES    := Generic \
	      TypesI EnvI ExprI ExprProp ExprSem \
	      SymI \
	      SubstI \
	      ProverI EProverI \
	      InstantiateI \
	      Lemma LemmaApply \
	      $(LAMBDA:%=Lambda/%) \
	      $(SUBST:%=Subst/%) \
	      $(UTIL:%=Util/%) \
	      $(STAC:%=STac/%) \
	      $(SYMS:%=syms/%) \
	      $(PROVERS:%=provers/%)

#	      $(EXTENSIBLE:%=Ext/%)
#	      $(POLY:%=Poly/%)
#	      $(LAMBDAM:%=LambdaM/%)


TESTS :=
VS         := $(GENERIC:%=%.v) $(MODULES:%=%.v)
TVS        := $(TESTS:%=%.v)

ARGS := -R . MirrorCore

.PHONY: coq clean package optimize

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
	@ ./../tools/deps.py $(MODULES:%=%.v.d) | sed '/coq_ext_lib/d' > ../deps.dot
	@ cat ../deps.dot | dot -Tpdf -o ../deps.pdf

wc:
	@ wc $(VS)

toplevel: coq
	coqtop.opt $(ARGS)

optimize:
	for x in $(VS); do echo $$x ; python ./../tools/opt-import.py $(ARGS) $$x ; done

-include ../Makefile.paths
