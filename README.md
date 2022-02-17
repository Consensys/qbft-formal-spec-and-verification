[![L1-Dafny-Safety-Verification](https://github.com/ConsenSys/qbft-formal-spec-and-verification/actions/workflows/L1-Dafny-Safety-Verification.yml/badge.svg)](https://github.com/ConsenSys/qbft-formal-spec-and-verification/actions/workflows/L1-Dafny-Safety-Verification.yml)

# QBFT Formal Specification and Verification

This repo contains the formal specification and verification of correctness of the QBFT consensus protocol which is based on the protocol described in the paper ["The Istanbul BFT Consensus Algorithm"](https://arxiv.org/abs/2002.03613) by Henrique Moniz.

## Repo Organization
- The formal specification of QBFT in Dafny can be found in the directory `<language>/spec`.
- The formal verification of QBFT in Dafny can be found in the directory `<language>/ver`.
- The directories `<language>/spec` and `<language>/ver` are organised according to the specification abstraction level where higher abstraction levels have lower number starting from 1. Hence, `L1` is the highest abstraction level possible and `L2` directories would contain a refinement of the specification contained in the `L1` directory.

## Current Status
- While the repo is orgnaised to allow for the formal specification and verification of QBFT in various languages, currently this repo only include the formal specification and verification of QBFT in Dafny.
- Only the `L1` specification is currently included in this repo.
- Formal verification of the liveness of QBFT is still pending.

## How to verify the Dafny spec
- `cd` to `dafny/ver/L1`
- execute `./verify.sh`
