#!/usr/bin/env bash

set -ev

eval $(opam config env)

opam repo add proofengineering-dev http://opam-dev.proofengineering.org

opam update

opam pin add toychain . --yes --verbose
