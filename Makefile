.PHONY: all clean build

all: build

build:
	dune build

clean:
	dune clean