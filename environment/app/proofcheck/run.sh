#!/bin/bash
# Builds, then checks every job the archive in this environment holds.
set -e
/app/proofcheck/build.sh
cd /app/proofcheck
exec /app/proofcheck/bin/proofcheck
