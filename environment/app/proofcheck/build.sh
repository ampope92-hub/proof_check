#!/bin/bash
# The build the grader runs: Main.hs as the root, the src tree on the search path, -O2.
set -e
mkdir -p /app/proofcheck/bin /tmp/proofcheck-build
ghc -O2 -i/app/proofcheck/src -outputdir /tmp/proofcheck-build -o /app/proofcheck/bin/proofcheck /app/proofcheck/src/Main.hs
