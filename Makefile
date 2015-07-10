coq: Makefile.coq
	$(MAKE) -C src
	$(MAKE) -f Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm Makefile.coq

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject -o Makefile.coq

dist:
	git archive --prefix=mirror-core/ -o mirror-core.tgz HEAD

install: coq
	$(MAKE) -f Makefile.coq install

init:
	@ ./tools/setup.sh -b $(EXTBRANCH)
	@ (cd coq-ext-lib; $(MAKE))


.PHONY: all clean dist init coq
