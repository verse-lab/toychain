# Toychain

[![Build Status](https://travis-ci.org/certichain/toychain.svg?branch=master)](https://travis-ci.org/certichain/toychain)

A Coq implementation of a minimalistic blockchain-based consensus protocol.

## Building the Project

### Requirements

* Coq 8.7 (available from https://coq.inria.fr/coq-87);
* Mathematical Components 1.6.4 (http://math-comp.github.io/math-comp/) (`ssreflect`)

### Building

We recommend installing requirements via [OPAM](https://opam.ocaml.org/doc/Install.html):
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-ssreflect
```

Then, run `make clean; make` from the root folder. This will build all
the libraries and check all the proofs.

## Project Structure

The top-level structure consists of the following folders:

* `Heaps` - a theory of partial finite maps by Nanevski et al.

* `Structures` - implementations of block forests and chain properties;

* `Systems` - definition of the protocol, its state, and network semantics;

* `Properties` - proved properties of the protocol, e.g., eventual
  consistency for a clique-like network topology;

### Obsolete development

* `Obsolete` -- properties that might or might not hold, as were
  verified out of many optimistically assumed axioms at the beginning
  of the project.

