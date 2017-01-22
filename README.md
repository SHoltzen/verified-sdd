# Verified SDD Compiler

## OCaml
### Building
* Use `ocaml` version `4.03.0`; other versions may work, but this is the one that I am using
* The following libraries are required: `OUnit2` `core`, `ppx_sexp_conv`, `sexplib`; these can all be installed from OPAM.
* With these libraries, you can build using the `Makefile` in `ml/`; this will generate `Sdd.native`; running this file will run the tests.
