all: default

default: Makefile.coq
	$(MAKE) -f Makefile.coq
	ocamlbuild -r -tag safe_string -libs unix -I +../sha -I Extraction/Extracted -I Shims Shims/test.d.byte

quick: Makefile.coq
	$(MAKE) -f Makefile.coq quick

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf

	# Added to remove extracted files
	rm -rf Extraction/Extracted/*
	rm -rf _build

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: all default quick install clean
