#!/bin/sh
(
    cd "$(dirname "$0")";
    time 'dafny-3.2.0' /compile:0  /vcsCores:8  /noCheating:1 /verifyAllModules theorems.dfy
)