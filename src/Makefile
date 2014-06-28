plugin: myocamlbuild.ml
	ocamlbuild mirror-core.otarget

clean:
	@ ocamlbuild -clean
	@ rm -f myocamlbuild.ml Makefile.paths
	@ rm -f *.cma *.cmxa *.cmxs

myocamlbuild.ml:
	@ ln -s $(COQLIB)user-contrib/PluginUtils/myocamlbuild.ml myocamlbuild.ml

Makefile.paths:
	@ coqc -config > Makefile.paths

include Makefile.paths
