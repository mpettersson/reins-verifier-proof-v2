all:
	OCAMLRUNPARAM="l=400M" ocamlopt -I ../REINS -c check.ml
	OCAMLRUNPARAM="l=400M" ocamlopt -o check.exe ../REINS/reinsverif.cmx check.cmx

clean:
	rm check.o check.cmx check.cmi