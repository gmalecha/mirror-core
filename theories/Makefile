GENERIC := CtxLogic
UTIL := Approx Iteration ListMapT Forwardy Quant Nat
PROVERS := ProverTac AssumptionProver DefaultProver AutoProver
SUBST   := UVarMap FMapSubst # CascadeSubst SealedSubst RawSubst2 FastSubst
EXTENSIBLE := Types ExprCore \
	      ExprT \
	      ExprDI ExprDFacts ExprD3 ExprD \
	      ExprLift ExprUnifySyntactic3 \
	      ExprSubst LemmaExt \
	      Expr ExprTactics \
	      SetoidFold AppFull Red AsConst \
	      provers/UnifyEProver
# ExprUnifySyntactic ExprUnifySyntactic2
LAMBDA := ExprCore ExprDI ExprDsimul ExprD ExprDFacts \
	  ExprTac \
	  Expr ExprLift Red RedAll \
	  TypedFoldEager TypedFoldLazy TypedFoldApp FoldApp StrongFoldApp \
	  WtExpr \
	  ExprUnify_common ExprUnify ExprUnify_simul \
	  ExprSubst ExprSubstitute AppN \
	  ExprVariables \
	  AutoSetoidRewrite
# ExprUnifyHO
LAMBDAM := ExprCore ExprCore_simul
POLY := Ctx Ctx2 TypeI ML ExprCore
STAC := Core Continuation Repeat \
	Apply EApply Rewrite Assumption \
	First Repeat Try Idtac Rec Solve Then Fail \
	Simplify Instantiate \
	UseForAll UseList \
	STac
RTAC := BIMap Ctx Core CoreK RunOnGoals \
	Then Try Repeat Rec Idtac First Fail Solve \
	Assumption \
	Intro Apply EApply \
	Simplify Instantiate \
	AtGoal Reduce \
	RTac
# Apply EApply
#	Continuation ApplyToAll
SYMS := SymEnv SymPolyEnv SymSum
REIFY := Patterns Reify
MODULES    := OpenT Generic \
	      TypesI EnvI ExprI VariablesI \
	      ExprProp ExprSem \
	      ExprDAs \
	      SymI \
	      SubstI \
	      ProverI EProverI \
	      InstantiateI \
	      Lemma LemmaApply \
	      $(PROVERS:%=provers/%) \
	      $(SUBST:%=Subst/%) \
	      $(UTIL:%=Util/%) \
	      $(SYMS:%=syms/%) \
	      $(RTAC:%=RTac/%) \
	      $(LAMBDA:%=Lambda/%) \
	      $(REIFY:%=Reify/%)

#	      $(STAC:%=STac/%)
#	      $(EXTENSIBLE:%=Ext/%)
#	      $(POLY:%=Poly/%)
#	      $(LAMBDAM:%=LambdaM/%)


TESTS :=
VS         := $(GENERIC:%=%.v) $(MODULES:%=%.v)
TVS        := $(TESTS:%=%.v)

ARGS := -R . MirrorCore -I ../src

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
