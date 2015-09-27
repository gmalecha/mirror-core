coq: Makefile.coq
	$(MAKE) -f Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject -o Makefile.coq

dist:
	git archive --prefix=mirror-core/ -o mirror-core.tgz HEAD

install: coq
	$(MAKE) -f Makefile.coq install

init:
	@ ./tools/setup.sh -b $(EXTBRANCH)
	@ (cd coq-ext-lib; $(MAKE))

check-imports:
	./tools/opt-import.py -p _CoqProject

deps.pdf:
	@ coqdep -dumpgraph deps.dot `sed '/COQLIB/d' _CoqProject` > /dev/null
	@ sed -i '/ext-lib/d' deps.dot
	@ dot -Tpdf deps.dot -o deps.pdf

.PHONY: all clean dist init coq deps.pdf check-imports

todo:
	git grep TODO
