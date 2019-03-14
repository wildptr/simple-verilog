.PHONY: all FORCE

all: Vlog_Parser_Test.native

%.native: FORCE
	ocamlbuild -use-ocamlfind -use-menhir -package extlib $*.native
