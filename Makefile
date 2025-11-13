.PHONY: build test

all: build

build:
	dune build duet --profile release

clean:
	dune clean

test:
	dune runtest --profile release -f

install:
	dune build @install
	dune install

uninstall:
	dune uninstall

doc:
	dune build @doc
