#!/bin/bash
# Reference solution: drop the finished checker into the project, build it the way the grader
# does, then read the archive here once so the build is not the only thing shown to work. The read
# is time bounded so an archive that is not up yet cannot hang the run.
set -e

cp -r /solution/src/. /app/proofcheck/src/
/app/proofcheck/build.sh

echo "built, checking the archive once"
cd /app/proofcheck
timeout 120 /app/proofcheck/bin/proofcheck || echo "the archive did not answer from here, which is fine at build time"
