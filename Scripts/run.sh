#!/usr/bin/env bash
(./node.native -me 127.0.0.1 9000 -cluster 127.0.0.1 9000 127.0.0.1 9001 127.0.0.1 9002 &) > node-00.log
(./node.native -me 127.0.0.1 9001 -cluster 127.0.0.1 9000 127.0.0.1 9001 127.0.0.1 9002 &) > node-01.log
(./node.native -me 127.0.0.1 9002 -cluster 127.0.0.1 9000 127.0.0.1 9001 127.0.0.1 9002 &) > node-02.log
