.PHONY: clean
clean:
	dune clean

.PHONY: build
build: clean
	dune build

.PHONY: test
test: build
	dune runtest -f

.PHONY: install
install: test
	dune install

.PHONY: format
format:
	dune build @fmt --auto-promote

.PHONY: deps
deps:
	opam install ppx_let yojson core
