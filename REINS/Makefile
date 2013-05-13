MODULES := Int32 PEFormat PETraversal ReinsVerifier ReinsVerifierDFA CompiledDFAs REINSjmp X86Lemmas DFACorrectness 
# ReinsVerifierCorrectness
VS 	:= $(MODULES:%=%.v)

.PHONY: coq clean

all: coq
	OCAMLRUNPARAM="l=400M" ocamlopt -c reinsverif.mli
	OCAMLRUNPARAM="l=400M" ocamlopt -c reinsverif.ml

coq: Makefile.coq 
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	echo $(VS)
	coq_makefile -I "../Model" $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
	rm reinsverif.mli reinsverif.ml reinsverif.cmx reinsverif.o
