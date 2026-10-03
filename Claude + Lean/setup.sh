#!/usr/bin/env bash
# One-time setup: use the same Lean version as Mathlib, download Mathlib, build the project.
set -e
cd "$(dirname "$0")"
curl -fsSL https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain
echo "Using $(cat lean-toolchain)"
lake update          # fetches Mathlib's source (a few minutes)
lake exe cache get   # downloads prebuilt Mathlib (several GB)
lake build           # checks the proofs in SingularMatrices/
