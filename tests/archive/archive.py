#!/usr/bin/env python3
"""The proof archive: serves each job's formula and proof in pages over a line protocol on TCP.

Everything it serves is read and cut into pages before the port opens; after that the only
shared state is the log.

  on connect               HELLO proof-archive <n>     (this connection answers n requests)
  JOBS                     JOBS <k>, then the k job names, one per line
  READ <job> <part> <tok>  PAGE <m> <next>, then m lines of <part> (cnf or proof) of <job>;
                           <tok> is start for the first page, then the <next> of the page
                           before; <next> is end on the last page
  anything else            ERR <reason>
After answering its n-th request the archive closes the connection. Page tokens stay good for
as long as the archive runs, on any connection.
"""
import argparse
import os
import random
import secrets
import socketserver
import sys
import threading


def load(data_dir, page, seed):
    rng = random.Random(seed)
    with open(os.path.join(data_dir, "jobs.txt")) as fh:
        names = [ln.strip() for ln in fh if ln.strip()]
    pages = {}   # (job, part, token) -> (bytes, next token)
    for name in names:
        for part, fname in (("cnf", "formula.cnf"), ("proof", "proof.drat")):
            with open(os.path.join(data_dir, name, fname), "rb") as fh:
                lines = fh.read().split(b"\n")
            if lines and lines[-1] == b"":
                lines.pop()
            cuts = []
            i = 0
            while True:
                m = rng.randint(max(1, page // 2), page)
                cuts.append((i, min(len(lines), i + m)))
                i += m
                if i >= len(lines):
                    break
            toks = ["start"] + [secrets.token_hex(8) for _ in cuts[1:]] + ["end"]
            for k, (a, b) in enumerate(cuts):
                body = b"".join(ln + b"\n" for ln in lines[a:b])
                head = b"PAGE %d %s\n" % (b - a, toks[k + 1].encode())
                pages[(name, part, toks[k])] = head + body
    return names, pages


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--data", required=True)
    ap.add_argument("--host", default="127.0.0.1")
    ap.add_argument("--port", type=int, default=7700)
    ap.add_argument("--page", type=int, default=4000, help="most lines in one page")
    ap.add_argument("--requests", type=int, default=64, help="requests one connection answers")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--ready-file", default="")
    ap.add_argument("--log", default="")
    a = ap.parse_args()

    names, pages = load(a.data, a.page, a.seed)
    jobs_answer = f"JOBS {len(names)}\n".encode() + b"".join(n.encode() + b"\n" for n in names)
    hello = f"HELLO proof-archive {a.requests}\n".encode()
    lock = threading.Lock()

    def log(msg):
        if a.log:
            with lock, open(a.log, "a") as fh:
                fh.write(msg + "\n")

    class Handler(socketserver.StreamRequestHandler):
        def handle(self):
            log("CONNECT")
            self.wfile.write(hello)
            served = 0
            while served < a.requests:
                raw = self.rfile.readline(4096)
                if not raw:
                    return
                words = raw.decode("ascii", "replace").split()
                if words == ["JOBS"]:
                    out = jobs_answer
                    log("JOBS")
                elif len(words) == 4 and words[0] == "READ" and (words[1], words[2], words[3]) in pages:
                    out = pages[(words[1], words[2], words[3])]
                    log(f"READ {words[1]} {words[2]} {'start' if words[3] == 'start' else 'token'}")
                else:
                    out = b"ERR unknown request\n"
                    log(f"ERR {raw[:80]!r}")
                self.wfile.write(out)
                served += 1
            log(f"CLOSE after {served}")

    class Server(socketserver.ThreadingTCPServer):
        allow_reuse_address = True
        daemon_threads = True

    srv = Server((a.host, a.port), Handler)
    if a.ready_file:
        with open(a.ready_file, "w") as fh:
            fh.write("ready\n")
    print(f"archive on {a.host}:{a.port}, {len(names)} jobs", file=sys.stderr, flush=True)
    srv.serve_forever()


if __name__ == "__main__":
    main()
