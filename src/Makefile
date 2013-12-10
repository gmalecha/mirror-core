# SRCS := $(wildcard *.ml) \
#         $(wildcard *.mli) \
#         $(wildcard *.ml4) \
#         $(wildcard *.mllib)


# .PHONY: coq clean package

# coq: Makefile.coq
# 	$(MAKE) -f Makefile.coq

# install: coq
# 	$(MAKE) -f Makefile.coq install

# Makefile.coq: Makefile $(SRCS)
# 	@ coq_makefile $(ARGS) -R . MirrorCore $(SRCS) -o Makefile.coq
# 	@ patch Makefile.coq < Makefile.patch

# Makefile.test.coq: Makefile $(TVS)
# 	coq_makefile $(ARGS) $(TVS) -o Makefile.test.coq

# test: coq Makefile.test.coq
# 	$(MAKE) -f Makefile.test.coq

# clean:: Makefile.coq
# 	$(MAKE) -f Makefile.coq clean
# 	rm -f Makefile.coq Makefile.test.coq .depend

# package:
# 	hg archive -t tgz /tmp/mirror-core.tgz

# admit:
# 	@ grep -n -e 'admit' -e 'Admitted' ${VS}

# depgraph: Makefile.coq
# 	@ echo Generating dependency graph to ../deps.pdf
# 	@ ./../tools/deps.py $(MODULES:%=%.v.d) > ../deps.dot
# 	@ ./../tools/deps.py $(MODULES:%=%.v.d) | dot -Tpdf -o ../deps.pdf

# toplevel: coq
# 	coqtop.opt $(ARGS)

# -include ../Makefile.paths

plugin: myocamlbuild.ml
	ocamlbuild mirror-core.otarget

clean:
	ocamlbuild -clean
	rm -f myocamlbuild.ml

myocamlbuild.ml:
	ln -s $(COQLIB)/user-contrib/PluginUtils/myocamlbuild.ml myocamlbuild.ml

Makefile.paths:
	@ coqc -config > Makefile.paths

include Makefile.paths
