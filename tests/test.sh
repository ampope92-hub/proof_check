#!/bin/bash

# Verifier entrypoint. Runs in the verifier container, not the agent's, and sees only the paths
# declared in `artifacts`. Everything it needs is baked into tests/Dockerfile; nothing is fetched
# here. The archives the graded runs talk to are started by this script from the copies in this
# image.

set -uo pipefail
cd /
mkdir -p /logs/verifier
echo 0 > /logs/verifier/reward.txt
exec 2>&1

LIMIT_S=60
AS_BYTES=2147483648

# Root runs this script and later runs pytest, after agent-authored code has run as the build
# user. Every directory on root's PATH has to be one the build user cannot write to; PATH is
# pinned rather than inherited and each entry is checked before anything untrusted runs.
export PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin
hash -r
for d in ${PATH//:/ }; do
  real="$(/usr/bin/readlink -f "$d" 2>/dev/null)" || continue
  [ -d "$real" ] || continue
  owner="$(/usr/bin/stat -c %u "$real")"
  mode="$(/usr/bin/stat -c %a "$real")"
  if [ "$owner" != "0" ] || [ $(( 8#$mode & 8#022 )) -ne 0 ]; then
    echo "FATAL: $d (-> $real) is on root's PATH but is owner $owner mode $mode; a file planted there would be run as root."
    exit 0
  fi
done
echo "every directory on root's PATH is root-owned and closed to writing by anyone else"

as_runner() {
  setpriv --clear-groups --no-new-privs --reuid runner --regid runner "$@"
}

/usr/bin/install -d -m 700 -o root -g root /opt/run

# One graded run reaches its archive by name: the README says PROOFS_HOST is a host name or an
# address.
ARCHIVE_BY_NAME=proofs.archive.internal
printf '%s\t%s\n' 127.0.0.3 "$ARCHIVE_BY_NAME" >> /etc/hosts
if ! /usr/bin/getent hosts "$ARCHIVE_BY_NAME" >/dev/null 2>&1; then
  echo "FATAL: $ARCHIVE_BY_NAME does not resolve in this container, so the named run cannot be graded."
  exit 0
fi

# Close the verifier's own code, the archives, the service and the reward directory to the build
# user before anything untrusted runs. `ls` needs read permission on the directory itself.
chmod 700 /tests /logs/verifier /opt/truth /opt/archive /opt/run 2>/dev/null || true
if as_runner bash -c 'test -r /tests/test_outputs.py || ls /opt/truth || ls /opt/archive || ls /opt/run || ls /logs/verifier' >/dev/null 2>&1; then
  echo "FATAL: /tests, the archives, the service or the run directory are still reachable by the unprivileged build user."
  exit 0
fi
echo "verifier files closed to the unprivileged build user"

# What is compiled is Haskell and nothing else: the regular .hs files under the collected src, kept
# by their paths below src, copied into a root-owned tree. Links, other files and everything
# outside src are left behind.
SRC_IN=/app/proofcheck/src
/usr/bin/rm -rf /opt/src_pristine
/usr/bin/install -d -m 755 -o root -g root /opt/src_pristine
if [ -d "$SRC_IN" ] && [ ! -L "$SRC_IN" ]; then
  while IFS= read -r -d '' f; do
    /usr/bin/install -D -m 644 -o root -g root "$SRC_IN/$f" "/opt/src_pristine/$f"
  done < <(cd "$SRC_IN" && /usr/bin/find . -type f -name '*.hs' -print0)
fi
echo "collected Haskell files: $(/usr/bin/find /opt/src_pristine -type f | /usr/bin/wc -l)"

wipe_scratch() {
  as_runner bash -c 'kill -9 -1' 2>/dev/null || true
  /usr/bin/find /tmp /var/tmp /dev/shm -mindepth 1 -maxdepth 1 ! -name 'pytest_cache' -exec /usr/bin/rm -rf {} + 2>/dev/null || true
  /usr/bin/rm -rf /home/runner
  /usr/bin/install -d -o runner -g runner -m 755 /home/runner
}

# Build once, as the build user, from a fresh tree: the documented ghc line and nothing else. The
# package environment files GHC would otherwise look for are switched off, and HOME is empty, so
# the only packages in reach are the global ones the README names. The build is bounded at 900 s.
echo failed > /opt/run/build_check.txt
wipe_scratch
/usr/bin/rm -rf /app/proofcheck
/usr/bin/install -d -o root -g root -m 755 /app/proofcheck
/usr/bin/cp -a /opt/src_pristine /app/proofcheck/src
/usr/bin/install -d -o runner -g runner -m 755 /app/proofcheck/bin /home/runner/ghc-out
/usr/bin/chown -R runner:runner /app/proofcheck/src
/usr/bin/find /app/proofcheck/src -type f -exec /usr/bin/touch {} +
setsid /usr/bin/timeout --signal=KILL 900 \
  setpriv --clear-groups --no-new-privs --reuid runner --regid runner \
  env -C /app/proofcheck HOME=/home/runner GHC_ENVIRONMENT=- \
    /usr/bin/ghc -O2 -i/app/proofcheck/src -outputdir /home/runner/ghc-out \
      -o /app/proofcheck/bin/proofcheck /app/proofcheck/src/Main.hs
status=$?
echo "ghc exit status: $status"
as_runner bash -c 'kill -9 -1' 2>/dev/null || true
if [ "$status" -eq 0 ] && [ -f /app/proofcheck/bin/proofcheck ] && [ ! -L /app/proofcheck/bin/proofcheck ]; then
  echo ok > /opt/run/build_check.txt
else
  echo "no regular binary was produced at /app/proofcheck/bin/proofcheck"
  /usr/bin/rm -rf /app/proofcheck/bin/proofcheck
fi
# From here on the binary and its directories belong to root, so no run can change what the
# next one executes.
/usr/bin/chown -R root:root /app/proofcheck
/usr/bin/chmod -R go-w /app/proofcheck

SERVICE_PID=""
start_archive() {   # $1 archive, $2 host, $3 port, $4 page lines, $5 requests per connection, $6 seed
  /usr/bin/rm -f /opt/run/ready
  /usr/local/bin/python3 /opt/archive/archive.py --data "/opt/truth/$1" --host "$2" --port "$3" \
      --page "$4" --requests "$5" --seed "$6" --ready-file /opt/run/ready \
      --log "/opt/run/archive_$1.log" >> "/opt/run/archive_$1.err" 2>&1 &
  SERVICE_PID=$!
  local i
  for i in $(/usr/bin/seq 1 1200); do
    [ -f /opt/run/ready ] && return 0
    /usr/bin/sleep 0.1
  done
  echo "FATAL: the archive never came up on $2:$3"
  return 1
}

# `kill` is the shell builtin on purpose: a builtin cannot be shadowed by anything on PATH.
stop_archive() {
  [ -n "$SERVICE_PID" ] || return 0
  kill -TERM "$SERVICE_PID" 2>/dev/null || true
  wait "$SERVICE_PID" 2>/dev/null
  SERVICE_PID=""
}

# $1 host, $2 port, $3 run name. The binary the build produced, from the directory the README
# documents, as the build user, with the stated wall time and address space, through tool_launch
# (tests/launch.c) so neither it nor any child can start another program. Its stdout is the
# report; the exit status and the wall time are recorded so a run is only called a timeout when
# it actually reached the limit.
run_checker() {
  local host="$1" port="$2" name="$3" pid rc t0 t1
  wipe_scratch
  if [ ! -x /app/proofcheck/bin/proofcheck ]; then
    : > "/opt/run/report_$name.txt"
    echo "127 0" > "/opt/run/status_$name.txt"
    return
  fi
  t0=$(/usr/bin/date +%s%N)
  setsid /usr/bin/timeout --signal=KILL "$LIMIT_S" \
    /usr/bin/prlimit --as="$AS_BYTES" -- \
    setpriv --clear-groups --no-new-privs --reuid runner --regid runner \
    env -i -C /app/proofcheck HOME=/home/runner PATH=/usr/bin:/bin LANG=C.UTF-8 \
      PROOFS_HOST="$host" PROOFS_PORT="$port" \
      /usr/local/bin/tool_launch /app/proofcheck/bin/proofcheck \
      < /dev/null > "/opt/run/report_$name.txt" 2> "/opt/run/stderr_$name.txt" &
  pid=$!
  wait "$pid"
  rc=$?
  t1=$(/usr/bin/date +%s%N)
  kill -KILL -- -"$pid" 2>/dev/null || true
  as_runner bash -c 'kill -9 -1' 2>/dev/null || true
  echo "$rc $(( (t1 - t0) / 1000000 ))" > "/opt/run/status_$name.txt"
  echo "run $name: exit status $rc after $(( (t1 - t0) / 1000000 )) ms, $(/usr/bin/wc -l < "/opt/run/report_$name.txt") report lines"
  /usr/bin/head -c 2000 "/opt/run/stderr_$name.txt"
}

echo "=== the archive the agent's environment serves, on another address and port, smaller pages, 6 requests a connection ==="
start_archive sample 127.0.0.2 7811 150 6 3 || exit 0
run_checker 127.0.0.2 7811 sample
stop_archive

echo "=== an archive the agent has never seen, reached by name, 40 requests a connection ==="
start_archive hidden 127.0.0.3 7812 5000 40 5 || exit 0
run_checker "$ARCHIVE_BY_NAME" 7812 hidden
stop_archive

for s in sample hidden; do
  echo "$s archive: $(/usr/bin/grep -c '^CONNECT' /opt/run/archive_$s.log) connections, $(/usr/bin/grep -c '^READ' /opt/run/archive_$s.log) pages read, $(/usr/bin/grep -c '^ERR' /opt/run/archive_$s.log) refused"
done
wipe_scratch

# By absolute path, and -P keeps the working directory off the module path.
/usr/local/bin/python3 -P -m pytest -o cache_dir=/tmp/pytest_cache \
  --ctrf /logs/verifier/ctrf.json /tests/test_outputs.py -rA
if [ "$?" -eq 0 ]; then echo 1 > /logs/verifier/reward.txt; else echo 0 > /logs/verifier/reward.txt; fi
