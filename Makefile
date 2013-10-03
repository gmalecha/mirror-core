MODULE:=MirrorCore

all:
	$(MAKE) -C src

clean:
	$(MAKE) -C src clean

dist:
	git archive --prefix=mirror-core/ -o mirror-core.tgz HEAD

.dir-locals.el: tools/dir-locals.el Makefile
	@ sed s,PWD,$(shell pwd -P),g tools/dir-locals.el | sed s,MOD,$(MODULE),g > .dir-locals.el

install:
	$(MAKE) -C src install

init:
	@ ./tools/setup.sh -b $(EXTBRANCH)
	@ (cd coq-ext-lib; $(MAKE))


.PHONY: all clean dist init

include Makefile.config