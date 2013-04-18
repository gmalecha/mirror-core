MODULE:=MirrorCore

.PHONY: all clean dist

all:
	$(MAKE) -C src

clean:
	$(MAKE) -C src clean

dist:
	git archive --format=tgz mirror-shard.tgz

.dir-locals.el: tools/dir-locals.el Makefile
	@ sed s,PWD,$(shell pwd -P),g tools/dir-locals.el | sed s,MOD,$(MODULE),g > .dir-locals.el

install: 
	$(MAKE) -C src install
