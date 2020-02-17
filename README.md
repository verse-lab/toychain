# Toychain

[![Build Status](https://travis-ci.org/certichain/toychain.svg?branch=master)](https://travis-ci.org/certichain/toychain)

A Coq implementation of a minimalistic blockchain-based consensus protocol.

## Building the Project

### Requirements

Coq definitions and proofs:

* [Coq 8.9 or later](https://coq.inria.fr)
* [Mathematical Components](http://math-comp.github.io/math-comp/) (`ssreflect`, 1.10)
* [FCSL PCM library](https://github.com/imdea-software/fcsl-pcm)

Executable node:

* [OCaml 4.06.0 or later](https://ocaml.org)
* [OCamlbuild](https://github.com/ocaml/ocamlbuild)
* [cryptokit](https://github.com/xavierleroy/cryptokit)
* [ipaddr](https://github.com/mirage/ocaml-ipaddr)

### Building Definitions and Proofs

We recommend installing the Coq requirements via [OPAM](https://opam.ocaml.org/doc/Install.html):
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq coq-mathcomp-ssreflect coq-fcsl-pcm
```

Then, run `make clean; make` from the root folder. This will build all
the libraries and check all the proofs.

### Building an Executable Node

The additional OCaml dependencies for the executable node can also
be installed via OPAM:
```
opam install ocamlbuild cryptokit ipaddr
```

Then, run `make node` from the root folder. This will produce an
executable named `node.native`.

## Project Structure

The top-level structure consists of the following folders:

* `Structures` - implementations of block forests and chain properties;

* `Systems` - definition of the protocol, its state, and network semantics;

* `Properties` - proved properties of the protocol, e.g., eventual
  consistency for a clique-like network topology;

