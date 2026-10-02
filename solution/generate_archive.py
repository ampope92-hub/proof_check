#!/usr/bin/env python3
"""Makes the proof archive's jobs: a CNF and a DRAT proof for each, and the verdict each earns.

    python3 generate_archive.py --archive sample --out DIR --golden FILE
    python3 generate_archive.py --archive hidden --out DIR --golden FILE

rebuild the two graded archives byte for byte (DIR/jobs.txt, DIR/<job>/formula.cnf,
DIR/<job>/proof.drat) and the report each must get. Every job comes from one seed by a fixed
recipe:

  * a chain of literals the CNF forces by unit propagation alone: a few unit clauses, then one
    reason clause per forced literal, some of them with a second reason;
  * blocks: four clauses over fresh variables g, a, b, c that the proof turns into (g a),
    (g -a) and the unit (g), after which it deletes the block, now satisfied; block clauses may
    carry a literal the chain makes false;
  * a clause chain over the units g that makes the empty clause RUP once every g is in;
  * clauses the chain satisfies, over filler variables;
  * extension definitions e <-> (x and y), RAT on e, on a fresh variable or on one whose only
    clause the proof deleted first;
  * what solvers write while they tidy up: a unit for a forced literal, a second reason learned
    later, the deletion of a reason once a unit or a second reason stands in for it, a clause
    learned again and one copy deleted, a unit deleted while its literal stays forced;
  * at most one planted defect: a block lemma after one of its clauses was deleted
    (dropped), a chain unit that leans on a deleted unit (unit), a block lemma whose false
    literal lost its only reason to a deletion (reason), an extension clause whose first
    literal is not its pivot (pivot).

Each archive also ends with one small RAT job (rat): in the sample archive the clauses written
out in RAT_SAMPLE below; held back, rat_job() from its seed, a lemma whose resolvents are RUP
without being tautological and then one whose middle resolvent is not RUP.

The verdict is the recipe's own claim. solution/independent_check.py derives every verdict again
from the files alone; its reports are tests/golden_ref/.
"""
import argparse
import json
import os
import random
import sys


class Job:
    def __init__(self, seed, p):
        self.r = random.Random(seed)
        self.p = p
        self.nv = 0
        self.cnf = []          # original clauses
        self.proof = []        # ('a' | 'd', [lits])
        self.forced = []       # chain literals, in the order the chain forces them
        self.reason = {}       # chain literal -> its (sole) original reason clause
        self.used = set()      # chain literals already spoken for by an event or a pad
        self.pad_queue = []    # literals that a later block must use as its pad
        self.filler = []
        self.fail_line = None

    def var(self):
        self.nv += 1
        return self.nv

    def shuf(self, c):
        c = list(c)
        self.r.shuffle(c)
        return c

    def add(self, c, first=None):
        c = self.shuf(c)
        if first is not None:
            c.remove(first)
            c.insert(0, first)
        self.proof.append(("a", c))
        return c

    def dele(self, c):
        self.proof.append(("d", self.shuf(c)))

    # ---- the chain -------------------------------------------------------------------------
    def build_chain(self):
        p, r = self.p, self.r
        roots = max(1, p["chain"] // 60)
        for _ in range(roots):
            v = self.var()
            lit = v if r.random() < 0.5 else -v
            self.cnf.append([lit])
            self.forced.append(lit)
        self.leaves = []
        self.parents_of = {}
        for _ in range(p["chain"]):
            v = self.var()
            y = v if r.random() < 0.5 else -v
            k = 1 if r.random() < 0.4 else 2
            ps = r.sample(self.forced[-min(len(self.forced), 400):], min(k, len(self.forced)))
            cl = [y] + [-q for q in ps]
            self.cnf.append(self.shuf(cl))
            self.reason[y] = cl
            self.parents_of[y] = ps
            if r.random() < p["second"]:
                qs = r.sample(self.forced, min(2, len(self.forced)))
                self.cnf.append(self.shuf([y] + [-q for q in qs]))
                self.reason[y] = None      # two reasons: not a candidate for events
            self.forced.append(y)
        # a literal nobody else's reason mentions is a leaf
        mentioned = set()
        for y, ps in self.parents_of.items():
            mentioned.update(ps)
        self.leaves = [y for y in self.forced[roots:] if y not in mentioned and self.reason.get(y)]
        r.shuffle(self.leaves)

    def take_leaf(self):
        while self.leaves:
            y = self.leaves.pop()
            if y not in self.used:
                self.used.add(y)
                return y
        raise SystemExit("ran out of leaf literals; raise chain")

    def pad(self):
        if self.pad_queue:
            return -self.pad_queue.pop(0)
        while True:
            t = self.r.choice(self.forced)
            if t not in self.used:
                return -t

    # ---- filler ----------------------------------------------------------------------------
    def build_filler(self):
        p, r = self.p, self.r
        self.filler = [self.var() for _ in range(p["filler"])]
        for _ in range(p["satisfied"]):
            while True:
                t = r.choice(self.forced)
                if t not in self.used:
                    break
            a, b = r.sample(self.filler, 2)
            self.cnf.append(self.shuf([t, a if r.random() < .5 else -a, b if r.random() < .5 else -b]))

    # ---- events ----------------------------------------------------------------------------
    def ev_extension(self, reuse=False, pivot_wrong=False):
        """e <-> (x and y) over filler x, y: three RAT lemmas on e."""
        r = self.r
        if reuse:
            e = self.var()
            d = [e] + [f if r.random() < .5 else -f for f in r.sample(self.filler, 2)]
            self.cnf.append(self.shuf(d))
            self.dele(d)
        else:
            e = self.var()
        x, y = r.sample(self.filler, 2)
        x = x if r.random() < .5 else -x
        y = y if r.random() < .5 else -y
        if pivot_wrong:
            # x also occurs negated in a clause the chain leaves open
            others = r.sample([f for f in self.filler if f not in (abs(x), abs(y))], 2)
            self.cnf.append(self.shuf([-x] + [f if r.random() < .5 else -f for f in others]))
            self.fail_line = len(self.proof) + 1
            self.add([-e, x], first=x)
            return
        self.add([-e, x], first=-e)
        self.add([-e, y], first=-e)
        self.add([e, -x, -y], first=e)

    def ev_second_reason(self):
        y = self.take_leaf()
        qs = self.r.sample([q for q in self.forced[: self.forced.index(y)] if q not in self.used], 2)
        self.used.update(qs)
        self.add([y] + [-q for q in qs])
        self.dele(self.reason[y])
        self.pad_queue.append(y)

    def ev_unit_then_reason(self):
        y = self.take_leaf()
        self.add([y])
        self.dele(self.reason[y])
        self.pad_queue.append(y)

    def ev_unit_deleted(self):
        y = self.take_leaf()
        self.add([y])
        self.dele([y])
        self.pad_queue.append(y)

    def fail_reason_deleted(self):
        y = self.take_leaf()
        self.dele(self.reason[y])
        self.pad_queue.insert(0, y)
        self.want_fail_block = True

    # ---- blocks ----------------------------------------------------------------------------
    def block(self, j, dup=False, drop_clause=False):
        g, a, b, c = (self.var() for _ in range(4))
        self.gs.append(g)
        B = [[g, a, b], [g, a, -b], [g, -a, c], [g, -a, -c]]
        forced_pad = None
        if self.pad_queue:
            forced_pad = self.pad()
            i = self.r.randrange(4)
            B[i] = B[i] + [forced_pad]
        for i in range(4):
            if len(B[i]) == 3 and self.r.random() < self.p["pad"]:
                B[i] = B[i] + [self.pad()]
        B = [self.shuf(x) for x in B]
        self.cnf.extend(B)
        if dup:
            k = self.r.randrange(2)
            self.add(B[k])
            self.dele(B[k])
        if getattr(self, "want_fail_block", False):
            self.want_fail_block = False
            which = next(i for i in range(4) if forced_pad in B[i])
            self.fail_line = len(self.proof) + 1 + (0 if which < 2 else 1)
        if drop_clause:
            self.dele(B[2 + self.r.randrange(2)])
            self.fail_line = len(self.proof) + 2
        self.add([g, a])
        self.add([g, -a])
        self.add([g])
        for x in B:
            self.dele(x)
        self.dele([g, a])
        self.dele([g, -a])
        return g

    def build(self, fail=None, fail_at=0.9):
        p, r = self.p, self.r
        self.build_chain()
        self.build_filler()
        nb = p["blocks"]
        self.gs = []
        # z chain: (-g1 z1) (-z1 -g2 z2) ... (-z_{m-1} -g_m); variables made now, clauses after
        zs = [self.var() for _ in range(nb - 1)]
        slots = ["er"] * p["ext"] + ["reuse"] * p["reuse"] + ["second"] * p["ev"] + \
                ["unitreason"] * p["ev"] + ["unitdel"] * p["ev"] + ["dup"] * p["dup"]
        per = [[] for _ in range(nb)]
        for s in slots:
            per[r.randrange(max(1, nb - 3))].append(s)
        fail_block = int(nb * fail_at)
        for j in range(nb):
            dup = False
            for s in per[j]:
                if s == "er":
                    self.ev_extension()
                elif s == "reuse":
                    self.ev_extension(reuse=True)
                elif s == "second":
                    self.ev_second_reason()
                elif s == "unitreason":
                    self.ev_unit_then_reason()
                elif s == "unitdel":
                    self.ev_unit_deleted()
                elif s == "dup":
                    dup = True
            if j == fail_block and self.fail_line is None:
                if fail == "pivot":
                    self.ev_extension(pivot_wrong=True)
                elif fail == "reason":
                    self.fail_reason_deleted()
            g = self.block(j, dup=dup, drop_clause=(fail == "dropped" and j == fail_block and self.fail_line is None))
            if fail == "unit" and j == fail_block and self.fail_line is None:
                self.dele([g])
                self.unit_gone = j
            gone = getattr(self, "unit_gone", None)
            if fail == "unit" and gone is not None and j == gone + 2:
                # the chain's newest link, which leans on the unit deleted two blocks back
                self.fail_line = len(self.proof) + 1
                self.add([zs[j - 1]])
            elif 0 < j and r.random() < p["zunit"] and not (gone is not None and j >= gone):
                # a unit the solver learns for the chain's newest link
                self.add([zs[j - 1]])
        # the combining chain, as original clauses
        g = self.gs
        self.cnf.append(self.shuf([-g[0], zs[0]]))
        for j in range(1, nb - 1):
            self.cnf.append(self.shuf([-zs[j - 1], -g[j], zs[j]]))
        self.cnf.append(self.shuf([-zs[nb - 2], -g[nb - 1]]))
        if fail == "unit" and self.fail_line is None:
            self.fail_line = len(self.proof) + 1
        self.proof.append(("a", []))
        # the order clauses are listed in says nothing
        r.shuffle(self.cnf)
        return self

    def verdict(self):
        return "OK" if self.fail_line is None else f"FAIL {self.fail_line}"

    def cnf_lines(self):
        yield f"p cnf {self.nv} {len(self.cnf)}"
        for c in self.cnf:
            yield " ".join(map(str, c)) + " 0"

    def proof_lines(self):
        for k, c in self.proof:
            s = " ".join(map(str, c))
            if k == "d":
                yield ("d " + s + " 0") if c else "d 0"
            else:
                yield (s + " 0") if c else "0"


RAT_SAMPLE = (3, [[3], [-1, 3]], [("a", [1, 2]), ("a", [])], 2)


def rat_job(seed):
    """A lemma (p q) that is not RUP and is RAT on p: every clause holding -p gives a resolvent
    that is RUP and not tautological, one of them only through propagation. Later a unit (s) that
    is not RUP, where -s sits in three clauses and only the middle one's resolvent is not RUP.
    Everything else is satisfied by literals the units force."""
    job = Job(seed, {})
    r = job.r
    n = r.randrange(40, 60)
    vs = list(range(1, n + 1))
    r.shuffle(vs)
    lits = [v if r.random() < .5 else -v for v in vs]
    u, w, x, y, v1, v, v2, p, q, s = lits[:10]
    filler = lits[10:]
    job.nv = n
    forced = [u, w, v1, v, v2]

    def fill():
        return [f if r.random() < .5 else -f for f in r.sample(filler, r.randrange(1, 4))]

    sat = [[r.choice(forced)] + fill() for _ in range(r.randrange(25, 40))]
    base = [[u], [-u, w], [x, y], [x, -y], [v1], [v], [-v1, v2], [-p, u], [-p, w] + fill()[:1], [-p, x]] + sat
    r.shuffle(base)
    third = len(base) // 3
    base.insert(r.randrange(2 * third, len(base)), [-s, v2] + fill()[:1])
    base.insert(r.randrange(third, 2 * third), [-s, -v])
    base.insert(r.randrange(0, third), [-s, v1])
    job.cnf = [job.shuf(c) for c in base]
    gone = r.sample(range(len(sat)), 6)

    def pads(k):
        for _ in range(k):
            if gone and r.random() < .3:
                job.dele(sat[gone.pop()])
            else:
                job.add([r.choice(forced)] + fill())
    pads(r.randrange(3, 9))
    job.add([p, q], first=p)
    pads(r.randrange(3, 9))
    job.fail_line = len(job.proof) + 1
    job.add([s])
    pads(r.randrange(2, 6))
    job.proof.append(("a", []))
    return job


def fixed_job(spec):
    nv, cnf, proof, fail_line = spec
    job = Job(0, {})
    job.nv, job.cnf, job.proof, job.fail_line = nv, cnf, proof, fail_line
    return job


def params(blocks, chain, filler, satisfied, ext, reuse, ev, dup, pad, second, zunit):
    return {"blocks": blocks, "chain": chain, "filler": filler, "satisfied": satisfied,
            "ext": ext, "reuse": reuse, "ev": ev, "dup": dup, "pad": pad, "second": second,
            "zunit": zunit}


SMALL_S = params(150, 500, 200, 400, 10, 4, 5, 3, 0.5, 0.10, 0.25)
SMALL_H = params(260, 380, 150, 300, 14, 5, 6, 4, 0.35, 0.18, 0.40)

# (seed, params, planted defect, where in the proof it goes)
ARCHIVES = {
    "sample": [
        (4101, params(3000, 2500, 1500, 3000, 400, 60, 25, 25, 0.5, 0.10, 0.20), None, 0.0),
        (4102, SMALL_S, "dropped", 0.62),
        (4103, SMALL_S, "unit", 0.80),
        (4104, SMALL_S, "reason", 0.71),
        (4105, SMALL_S, "pivot", 0.55),
    ],
    "hidden": [
        (9301, params(120000, 100000, 20000, 100000, 20000, 2000, 25, 300, 0.4, 0.15, 0.15), "reason", 0.97),
        (9302, params(5000, 1500, 2500, 2000, 700, 90, 30, 30, 0.7, 0.2, 0.3), None, 0.0),
        (9303, SMALL_H, "dropped", 0.83),
        (9304, SMALL_H, "unit", 0.66),
        (9305, SMALL_H, "reason", 0.58),
        (9306, SMALL_H, "pivot", 0.77),
    ],
}

# the small RAT job each archive ends with, by name
RAT_JOBS = {
    "sample": ("run-5583", lambda: fixed_job(RAT_SAMPLE)),
    "hidden": ("cnf-6412", lambda: rat_job(9307)),
}


def write_job(job, path):
    os.makedirs(path, exist_ok=True)
    with open(os.path.join(path, "formula.cnf"), "w") as fh:
        fh.writelines(ln + "\n" for ln in job.cnf_lines())
    with open(os.path.join(path, "proof.drat"), "w") as fh:
        fh.writelines(ln + "\n" for ln in job.proof_lines())


def build_archive(which, out, golden):
    spec = ARCHIVES[which]
    rng = random.Random(sum(s for s, _, _, _ in spec))
    names = []
    for _ in spec:
        while True:
            nm = f"{rng.choice(['cnf', 'sat', 'job', 'run'])}-{rng.randrange(10000):04d}"
            if nm not in names:
                names.append(nm)
                break
    order = list(range(len(spec)))
    rng.shuffle(order)
    lines = []
    for k in order:
        seed, p, fail, at = spec[k]
        job = Job(seed, p).build(fail, at)
        write_job(job, os.path.join(out, names[k]))
        lines.append(f"{names[k]} {job.verdict()}")
        print(f"{names[k]} seed {seed} vars {job.nv} clauses {len(job.cnf)} "
              f"proof {len(job.proof)} -> {job.verdict()}", file=sys.stderr)
    name, make = RAT_JOBS[which]
    job = make()
    write_job(job, os.path.join(out, name))
    lines.append(f"{name} {job.verdict()}")
    with open(os.path.join(out, "jobs.txt"), "w") as fh:
        fh.write("".join(ln.split()[0] + "\n" for ln in lines))
    if golden:
        with open(golden, "w") as fh:
            fh.write("".join(ln + "\n" for ln in lines))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--archive", choices=sorted(ARCHIVES))
    ap.add_argument("--out", required=True)
    ap.add_argument("--golden", default="")
    # one job by hand, for calibration
    ap.add_argument("--seed", type=int)
    ap.add_argument("--params")
    ap.add_argument("--fail", default=None)
    ap.add_argument("--fail-at", type=float, default=0.9)
    a = ap.parse_args()
    if a.archive:
        build_archive(a.archive, a.out, a.golden)
        return
    job = Job(a.seed, json.loads(a.params)).build(a.fail, a.fail_at)
    write_job(job, a.out)
    with open(os.path.join(a.out, "verdict.txt"), "w") as fh:
        fh.write(job.verdict() + "\n")
    print(job.verdict(), "vars", job.nv, "clauses", len(job.cnf), "proof", len(job.proof), file=sys.stderr)


if __name__ == "__main__":
    main()
