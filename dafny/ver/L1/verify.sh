#!/bin/sh
# TODO Use advanced verify
(
    cd "$(dirname "$0")";
    time docker run -it --rm -v $PWD/../../..:/dafnyhome -u $(id -u) xtrm0/dafny:3.3.0 dafny /compile:0  /vcsCores:8  /noCheating:1 /verifyAllModules dafny/ver/L1/theorems.dfy
)