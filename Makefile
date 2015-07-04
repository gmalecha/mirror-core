coq: Makefile.coq
	$(MAKE) -f Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq -arg -type-in-type

dist:
	git archive --prefix=mirror-core/ -o mirror-core.tgz HEAD

install: coq
	$(MAKE) -f Makefile.coq install

init:
	@ ./tools/setup.sh -b $(EXTBRANCH)
	@ (cd coq-ext-lib; $(MAKE))


.PHONY: all clean dist init coq
