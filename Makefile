all: default

default: Makefile.coq
	cp Structures/AbstractParameters.v Structures/Parameters.v
	$(MAKE) -f Makefile.coq
	rm Structures/Parameters.v

extract: Makefile.coq
	cp Extraction/Impl.v Structures/Parameters.v
	$(MAKE) -f Makefile.coq
	rm Structures/Parameters.v

quick: Makefile.coq
	$(MAKE) -f Makefile.coq quick

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: all default quick install clean
