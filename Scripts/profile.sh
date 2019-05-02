#!/usr/bin/env sh
# Make the executable profilable without running as root
(perf record --call-graph=dwarf -- ./node.native -me 0 0 127.0.0.1 9000 1 127.0.0.1 9001 2 127.0.0.1 9002 &) > node-00.log
(./node.native -me 1 0 127.0.0.1 9000 1 127.0.0.1 9001 2 127.0.0.1 9002 &) > node-01.log
(./node.native -me 2 0 127.0.0.1 9000 1 127.0.0.1 9001 2 127.0.0.1 9002 &) > node-02.log
