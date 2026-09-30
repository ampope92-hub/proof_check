# Verifier image. Runs in its own container, sees only the paths declared in `artifacts`, and holds
# everything the agent never sees: the held-back archive, the report each archive must get, and
# the archive service that serves them. It compiles the collected Haskell itself and runs the
# checker against archives it starts, so every verdict has to come out of the agent's own
# program talking the protocol.

# The checker is started through tests/launch.c, which lets it start no other program. It is
# built statically in a throwaway stage.
FROM public.ecr.aws/docker/library/python:3.13-slim-bookworm@sha256:01f42367a0a94ad4bc17111776fd66e3500c1d87c15bbd6055b7371d39c124fb AS launcher
RUN apt-get update && apt-get install -y --no-install-recommends gcc libc6-dev && rm -rf /var/lib/apt/lists/*
COPY launch.c /tmp/launch.c
RUN gcc -O2 -static -Wall -o /tool_launch /tmp/launch.c

FROM public.ecr.aws/docker/library/python:3.13-slim-bookworm@sha256:01f42367a0a94ad4bc17111776fd66e3500c1d87c15bbd6055b7371d39c124fb

ENV LANG=C.UTF-8 \
    LC_ALL=C.UTF-8 \
    PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin

# The same GHC 9.0.2 and network library the agent's box has, from Debian bookworm, and the
# verifier tooling from a hash-pinned lockfile. Nothing is installed at trial time.
RUN apt-get update \
    && apt-get install -y --no-install-recommends ghc libghc-network-dev \
    && rm -rf /var/lib/apt/lists/*
COPY requirements.txt /tmp/requirements.txt
RUN pip install --no-cache-dir --require-hashes --no-deps -r /tmp/requirements.txt && rm -f /tmp/requirements.txt

COPY --from=launcher /tool_launch /usr/local/bin/tool_launch
RUN useradd --create-home --uid 10001 --shell /bin/bash runner

# Landing directory for the declared artifact.
RUN mkdir -p /app/proofcheck/src

# The archives, the reports and the service, root only. The held-back archive is too large to
# ship as files, so it is generated here from the same recipe as solution/generate_archive.py
# and must hash to the manifest, byte for byte, or the image does not build.
COPY data/sample /opt/truth/sample
COPY golden /opt/truth/golden
COPY archive /opt/archive
COPY data/hidden.sha256 /opt/truth/hidden.sha256
RUN python3 /opt/archive/generate_archive.py --archive hidden --out /opt/truth/hidden --golden /opt/truth/hidden_recipe.txt \
    && cd /opt/truth/hidden && sha256sum --quiet -c /opt/truth/hidden.sha256 \
    && cmp /opt/truth/hidden_recipe.txt /opt/truth/golden/hidden.txt \
    && chmod 700 /opt/truth /opt/archive

# Separate mode does not upload tests/ into the image, so the image owns /tests itself.
COPY . /tests/

WORKDIR /app/proofcheck
