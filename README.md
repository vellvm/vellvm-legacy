# Vellvm-Legacy

This is a "sanitized" copy of the original Vellvm repo, not including
publication sources, experiment results, and code, test cases, and benchmarks
that we don't have the right to redistribute. Sources for the required modified
third-party libraries have been removed from the history instead provided via
patches.

The modified OCaml bindings used for the Parser, Interpreter, and
verified instrumentation/optimization passes have diverged significantly from
what is availble with newer versions of LLVM and will not compile. Neither the
bindings, SoftBound or Vmem2reg passes are currently included in the
repository. It is possible to extract the interpreter, but there is currently no
way to parse LLVM bitcode into a Vellvm AST.

## Dependencies

- camlp4 (For equations plugin -- no longer included with OCaml as of 4.02)
- Coq 8.4pl4
- [ott 0.24](http://www.cl.cam.ac.uk/~pes20/ott/)

## Building

1. In the top-level directory of the repo, run `scripts/fetch-libs.sh` to
download all third-party sources into lib/src, extract, and apply patches.
2. Run `make libs` to compile the Equations plugin and the metatheory
library. If you get an error about grammar.cma, make sure your version of coq
was compiled with the same version of OCaml in your path.
3. Run `make` to compile the Vellvm theories.
