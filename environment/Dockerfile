# The checker's box. Nothing from tests/ or solution/ is copied in here, and neither is the
# archive's data: the jobs live in the archive service's own image and are only reachable over
# its socket.
FROM public.ecr.aws/docker/library/python:3.13-slim-bookworm@sha256:01f42367a0a94ad4bc17111776fd66e3500c1d87c15bbd6055b7371d39c124fb

ENV LANG=C.UTF-8 \
    LC_ALL=C.UTF-8

# GHC 9.0.2 and the network library, both from Debian bookworm. The grader's image installs the
# same two packages, so a program that builds here builds there.
RUN apt-get update \
    && apt-get install -y --no-install-recommends \
        asciinema \
        ca-certificates \
        ghc \
        libghc-network-dev \
        tmux \
    && rm -rf /var/lib/apt/lists/*
RUN ghc --version

# Where the archive is. The grader points these somewhere else.
ENV PROOFS_HOST=127.0.0.1 \
    PROOFS_PORT=7700

WORKDIR /app/proofcheck
COPY app/proofcheck/ /app/proofcheck/
RUN chmod +x /app/proofcheck/build.sh /app/proofcheck/run.sh
