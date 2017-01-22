# Makefile
main:
	ocamlbuild -cflag -g -use-ocamlfind Sdd.native
clean:
	ocamlbuild -clean
test:
	ocamlbuild -cflag -g -use-ocamlfind Test.native

.PHONY: main clean
