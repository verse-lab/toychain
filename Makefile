all: default

default: Makefile.coq
	mkdir -p Extraction/src/toychain
	$(MAKE) -f Makefile.coq
	ocamlbuild node.byte -r -I Extraction/src -I Extraction/src/toychain

quick: Makefile.coq
	$(MAKE) -f Makefile.coq quick

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf
	rm -rf Extraction/src/toychain
	rm -rf _build/
	rm -rf *.byte *.native

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: all default quick install clean
