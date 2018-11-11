# Frontend to dune.

.PHONY: default build install uninstall test clean

default: build

build:
	dune build runprf.exe

test:
	dune runtest -f

install:
	dune install

uninstall:
	dune uninstall

clean:
	dune clean
