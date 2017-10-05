# Toychain

An Coq implementation of a minimalistic blockchain-based consensus protocol.

## Building the Project

### Requirements

* Coq 8.5pl2 or 8.6 (available from https://coq.inria.fr/download)
* Mathematical Components 1.6.1 (http://math-comp.github.io/math-comp/)

### Building

Run `make clean; make` from the root folder. This will build all
the libraries and will check all the proofs.

## Project Structure

The top-level structure consits of the following folders:

* `Heaps` - a theory of partial finite maps by Nanevski et al.

* `Structures` - implementations of block forests and chain properties;

* `Systems` - definitino of the protocol, its state, and network semantics;

* `Properties` - proved properties of the protocol, e.g., eventual
  consistency for a clique-like network topology;

### Obsolete development

* `Obsolete` -- properties that might or might not hold, as were
  verified out of many optimistically assumed axioms at the beginning
  of the project.

