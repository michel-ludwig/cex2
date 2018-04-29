all: cex

cex:: # rule with no dependencies, is always triggered
	ocamlbuild -lib unix -lib str -I cb/main -I cb/libs cex2.native
	mv _build/cex2.native ./cex25
	unlink cex2.native

clean: 
	ocamlbuild -clean;
