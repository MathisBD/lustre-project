# Author

Mathis Bouverot-Dupuis

# Description

This is the project for an M1 synchronous programming course by Marc Pouzet and Timothy Bourke. It is a type-checker for a simplified version of lustre, which performs a couple syntactic analyses. Parsing, type checking and scheduling are taken from `mini-lustre`, and I added initialization checking.

# Building and running

This project requires a working opam installation. To install dependencies, create a local opam switch `opam switch create . 4.14.2 -y` and install dependencies `opam install . --deps-only --working-dir`.

You can then build the project by running `dune build` and run the main executable on some input file `input.mls` by running `dune exec exe/minilustre.exe -- input.mls`. Currently it prints the inferred type
of each node, or an error if a node is not well initialized.

# File structure

- /exe contains the main executable `minilustre`. 
- /examples contains a few lustre programs to test the executable.
- /lib contains the code for the various analyses. Parsing, typing and scheduling are kept mostly unchanged from mini-lustre. Initialization is implemented in `initialization.ml`, and constraint simplification is implemented in `delay_types.ml`.

