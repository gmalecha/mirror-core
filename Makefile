all: coq plugin

coq:
	$(MAKE) -C theories

plugin:
	$(MAKE) -C src

clean:
	$(MAKE) -C theories clean
	$(MAKE) -C src clean

dist:
	git archive --prefix=mirror-core/ -o mirror-core.tgz HEAD

.dir-locals.el: tools/dir-locals.el Makefile
	@ sed s,PWD,$(shell pwd -P),g tools/dir-locals.el | sed s,MOD,$(MODULE),g > .dir-locals.el

install:
	$(MAKE) -C theories install

init:
	@ ./tools/setup.sh -b $(EXTBRANCH)
	@ (cd coq-ext-lib; $(MAKE))


.PHONY: all clean dist init coq plugin
