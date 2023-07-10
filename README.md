# Coq with Observational Equality

Coq is a formal proof management system. It provides a formal language to write
mathematical definitions, executable algorithms and theorems together with an
environment for semi-interactive development of machine-checked proofs.

This branch is an implementation of observational equality using `SProp` and 
rewrite rules, this is done in "init/Logic.v".

The file "pretyping/observational.ml" provides support for the generation
of projection of equality and rewrite rules for casts when defining a new inductive type. 

For this generation to be turned on, the user should type

``` Coq 
Set Observational Inductives.
```

while having universe polymorphism already turned on.

The file "observational.v" at the root of the repository provides 
basic uses of observational equality in Coq.

## Installation

To compile this version of Coq, you need:

- [OCaml](https://ocaml.org/) (version >= 4.09.0)
  (This version of Coq has been tested with OCaml 5.0.0)

- The [Dune OCaml build system](https://github.com/ocaml/dune/) >= 2.9.1
  (This version of Coq has been tested with dune 3.7.1)


- The [findlib](http://projects.camlcity.org/projects/findlib.html) library (version >= 1.8.1)

- GNU Make (version >= 3.81)

To install this version of Coq, you should only have to type

```
make world
```

in your terminal.