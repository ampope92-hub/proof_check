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
without being tautological and then one whose middle resolvent is not RUP. After it come the
edge jobs: in the sample archive EMPTY_SAMPLE (an empty clause in the CNF) and TAB_WIDE_SAMPLE
(tabs between literals, eight-literal clauses); held back, edge_job() from its seed, all three.
Last come the cases written out in EMPTY_CNF_SAMPLE, STOP_SAMPLE and WIDE_RAT_SAMPLE (a CNF with
no clauses, steps after an accepted empty clause, a RAT resolvent of nine literals); held back,
the same from seeds, with steps after an accepted empty clause twice. Last of all, the clauses
written out in OVERLAP_SAMPLE (a RAT resolvent that shares a literal, same sign, with the lemma
itself); held back, overlap_job() from its seed, where that resolvent is RUP only through a chain
of units and the proof goes on past it. The sample archive then has MULTI_EMPTY_SAMPLE (two empty
clauses in the CNF, one deleted) and TOP_VAR_SAMPLE (variable 1000000); held back,
multi_empty_job() from its seed, and the held-back archive starts with top_var_job().

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


class RawJob:
    """A job given as its lines, separators and all."""
    def __init__(self, cnf, proof, fail_line):
        self.cnf, self.proof, self.fail_line = cnf, proof, fail_line

    verdict = Job.verdict

    def cnf_lines(self):
        return iter(self.cnf)

    def proof_lines(self):
        return iter(self.proof)


# the empty clause is in the CNF, so every addition is RUP
EMPTY_SAMPLE = (["p cnf 1 1", "0"], ["0"], None)

# (1 2) and (-1 2) are written with a tab after the first literal; with units -3 ... -9 the
# eight-literal clauses force 10 and 11, and the empty clause at the end is not RUP
TAB_WIDE_SAMPLE = (
    ["p cnf 11 11", "1\t2 0", "-1\t2 0"] + [f"-{v} 0" for v in range(3, 10)]
    + ["3 4 5 6 10 7 8 9 0", "3 4 5 11 6 7 8 9 0"],
    ["10 11 3 4 5 6 7 8 0", "d\t10\t11 3 4 5 6 7 8 0", "0"], 3)


def edge_job(seed):
    """Held back: the CNF holds the empty clause, so the first lemma (u) is accepted though it is
    neither RUP nor RAT without it; the proof then deletes (u) and the empty clause. Seven units
    make two eight-literal clauses force f1 and f2, f1 after the fourth literal and f2 before the
    fifth. (x y) and (-x y) are written with a tab after x, other lines with tabs at random,
    filler clauses of two to eight literals each hold one unit literal. The empty clause at the
    end is not RUP."""
    r = random.Random(seed)
    n = r.randrange(40, 60)
    vs = list(range(1, n + 1))
    r.shuffle(vs)
    lits = [v if r.random() < .5 else -v for v in vs]
    x, y, u, v, w, f1, f2 = lits[:7]
    units = lits[7:14]
    filler = lits[14:]

    def wide(f, lo, hi):
        c = [-t for t in units]
        r.shuffle(c)
        c.insert(r.randrange(lo, hi + 1), f)
        return c

    def sat():
        k = r.randrange(1, 8)
        return r.sample([r.choice(units)] + [f if r.random() < .5 else -f for f in r.sample(filler, k)], k + 1)

    w1, w2 = wide(f1, 4, 7), wide(f2, 0, 3)
    body = [[t] for t in units] + [w1, w2, [-u, v, w]] + [sat() for _ in range(r.randrange(12, 20))]
    r.shuffle(body)

    def line(c, tabbed=None):
        if tabbed is None:
            tabbed = r.random() < .4
        out = ""
        for k, t in enumerate(c + [0]):
            out += (("\t" if tabbed and r.random() < .6 else " ") if k else "") + str(t)
        return out

    cnf = [line(c) for c in body]
    cnf.insert(r.randrange(len(cnf) + 1), "0")
    cnf.insert(r.randrange(len(cnf) + 1), f"{-x}\t{y} 0")
    cnf.insert(r.randrange(len(cnf) + 1), f"{x}\t{y} 0")
    proof = [f"{u} 0", f"d {u} 0", "d 0"]
    lemmas = [r.sample([f1, f2] + [-t for t in r.sample(units, 6)], 8) for _ in range(r.randrange(2, 5))]
    for c in lemmas:
        proof.append(line(c))
    proof.append(line(r.sample(units, 1)))
    for c in r.sample(lemmas, len(lemmas)):
        proof.append("d\t" + line(r.sample(c, len(c)), tabbed=True))
    proof.append("0")
    return RawJob([f"p cnf {n} {len(cnf)}"] + cnf, proof, len(proof))


# no clauses at all: the empty clause is not RUP
EMPTY_CNF_SAMPLE = (["p cnf 1 0"], ["0"], 1)

# the empty clause added from the two units, deleted with both units; the final one is not RUP
STOP_SAMPLE = (["p cnf 1 2", "1 0", "-1 0"], ["0", "d 0", "d 1 0", "d -1 0", "0"], 5)

# (1 ... 8) is RAT on 1 only through its resolvent with (-1 9), nine literals
WIDE_RAT_SAMPLE = (["p cnf 9 2", "9 0", "-1 9 0"], ["1 2 3 4 5 6 7 8 0", "0"], 2)

# (1 2) is not RUP and is RAT on 1 only through (-1 2 3): the resolvent {1,2,3} shares 2, same
# sign, with the lemma itself; it is RUP only because (3 4) and (3 -4) force opposite units once
# 3 is false. The empty clause at the end is not RUP.
OVERLAP_SAMPLE = (4, [[-1, 2, 3], [3, 4], [3, -4]], [("a", [1, 2]), ("a", [])], 2)


def lits_of(seed):
    r = random.Random(seed)
    n = r.randrange(30, 50)
    vs = list(range(1, n + 1))
    r.shuffle(vs)
    return r, n, vs


def text(c):
    return " ".join(map(str, c + [0]))


def empty_cnf_job(seed):
    """Held back: a CNF with no clauses. Every lemma is RAT on a fresh positive first literal (no
    negative literal appears anywhere), one is deleted, and the empty clause at the end is not RUP."""
    r, n, vs = lits_of(seed)
    seen, proof = [], []
    for _ in range(r.randrange(3, 7)):
        p = vs.pop()
        proof.append(text([p] + r.sample(seen, min(len(seen), r.randrange(0, 4)))))
        seen.append(p)
    proof.insert(r.randrange(1, len(proof) + 1), "d " + proof[0])
    proof.append("0")
    return RawJob([f"p cnf {n} 0"], proof, len(proof))


def stop_job(seed, reject_lemma):
    """Held back: units t and -t make the empty clause RUP, so it and a few positive lemmas are
    accepted; the proof then deletes the empty clause and both units and goes on with lemmas RAT
    on fresh positive literals. With reject_lemma a unit (a) is rejected there, (-a b) being in
    the CNF; otherwise the final empty clause is. Every other CNF clause is positive."""
    r, n, vs = lits_of(seed)
    t = vs.pop()
    a, b = vs.pop(), vs.pop()
    filler = vs[: len(vs) // 2]
    fresh = vs[len(vs) // 2:]
    cnf = [[t], [-t]] + [r.sample(filler, r.randrange(2, 5)) for _ in range(r.randrange(6, 12))]
    if reject_lemma:
        cnf.append(r.sample([-a, b], 2))
    r.shuffle(cnf)
    proof = ["0"] + [text(r.sample(filler, r.randrange(1, 4))) for _ in range(r.randrange(1, 4))]
    proof += r.sample(["d 0", f"d {t} 0", f"d {-t} 0"], 3)
    for _ in range(r.randrange(2, 5)):
        proof.append(text([fresh.pop()] + r.sample(filler, r.randrange(0, 3))))
    fail = None
    if reject_lemma:
        proof.append(f"{a} 0")
        fail = len(proof)
        proof.append(text([fresh.pop()]))
    proof.append("0")
    return RawJob([f"p cnf {n} {len(cnf)}"] + [text(c) for c in cnf], proof, fail or len(proof))


def wide_rat_job(seed):
    """Held back: an eight-literal lemma (p ...) over fresh variables is not RUP; it is RAT on p
    through its one resolvent with (-p d1 .. dk), which is RUP only because of (d1 .. dk -m) and
    the unit (m), so the resolvent needs all of its 8 + k literals. The empty clause at the end
    is not RUP; the other clauses hold m."""
    r, n, vs = lits_of(seed)
    sign = [v if r.random() < .5 else -v for v in vs]
    m, p = sign.pop(), sign.pop()
    c = [p] + [sign.pop() for _ in range(7)]
    d = [sign.pop() for _ in range(r.randrange(2, 5))]
    cnf = [[m], r.sample([-p] + d, len(d) + 1), r.sample(d + [-m], len(d) + 1)]
    cnf += [r.sample([m] + r.sample(sign, k), k + 1) for k in (r.randrange(1, 4) for _ in range(r.randrange(5, 10)))]
    r.shuffle(cnf)
    proof = [text(c[:1] + r.sample(c[1:], 7)), text([m]), "0"]
    return RawJob([f"p cnf {n} {len(cnf)}"] + [text(x) for x in cnf], proof, 3)


def overlap_job(seed):
    """Held back: a lemma (p q), written with p first, is not RUP and is RAT on p through three
    clauses holding -p. The resolvent with (-p q w) shares q, same sign, with the lemma and is RUP
    only through four units in a row once w is false: (w k1), (-k1 k2), (-k2 k3), then (-k3 t) and
    (-k3 -t) clash. The other two resolvents are RUP through the units f and u, (-u v). RUP lemmas
    come before and after it; later a unit (s) with (-s x) in the CNF is rejected. Every other
    clause holds a forced literal."""
    r, n, vs = lits_of(seed)
    sign = [v if r.random() < .5 else -v for v in vs]
    p, q, w, k1, k2, k3, t, f, u, v, s, x = (sign.pop() for _ in range(12))
    filler = sign
    forced = [f, u, v]

    def fill():
        return [y if r.random() < .5 else -y for y in r.sample(filler, r.randrange(1, 4))]

    cnf = [[-p, q, w], [w, k1], [-k1, k2], [-k2, k3], [-k3, t], [-k3, -t], [-p, f], [-p, v],
           [f], [u], [-u, v], [-s, x]] + [[r.choice(forced)] + fill() for _ in range(r.randrange(8, 14))]
    cnf = [r.sample(c, len(c)) for c in cnf]
    r.shuffle(cnf)

    def pads(k):
        return [text(r.sample(c, len(c))) for c in ([r.choice(forced)] + fill() for _ in range(k))]
    proof = pads(r.randrange(3, 7)) + [text([p, q])] + pads(r.randrange(3, 7))
    proof.append(text([s]))
    fail = len(proof)
    proof += pads(r.randrange(1, 4)) + ["0"]
    return RawJob([f"p cnf {n} {len(cnf)}"] + [text(c) for c in cnf], proof, fail)


# two empty clauses in the CNF; the proof deletes one, so the empty clause added after is RUP
MULTI_EMPTY_SAMPLE = (["p cnf 1 2", "0", "0"], ["d 0", "0"], None)

# the largest variable a job may have
TOP_VAR_SAMPLE = (["p cnf 1000000 2", "1000000 0", "-1000000 0"], ["0"], None)


def multi_empty_job(seed):
    """Held back: three empty clauses in the CNF. The proof deletes them one at a time, with RUP
    lemmas between; the unit (x), (-x y) being in the CNF, is accepted only because an empty clause
    is still there. After the third deletion a unit (z), (-z w) being in the CNF, is rejected."""
    r, n, vs = lits_of(seed)
    sign = [v if r.random() < .5 else -v for v in vs]
    f1, f2, x, y, z, w = (sign.pop() for _ in range(6))
    filler = sign
    forced = [f1, f2]

    def pads(k):
        return [text(r.sample(c, len(c))) for c in
                ([r.choice(forced)] + [g if r.random() < .5 else -g for g in r.sample(filler, r.randrange(1, 4))]
                 for _ in range(k))]
    cnf = [text(c) for c in [[f1], [f2], r.sample([-x, y], 2), r.sample([-z, w], 2)]] + pads(r.randrange(8, 14))
    for _ in range(3):
        cnf.insert(r.randrange(len(cnf) + 1), "0")
    proof = pads(r.randrange(1, 4)) + ["d 0", text([x])] + pads(r.randrange(1, 4)) + ["d 0"]
    proof += pads(r.randrange(1, 4)) + ["d 0"] + pads(r.randrange(2, 5)) + [text([z])]
    fail = len(proof)
    proof += pads(r.randrange(1, 3)) + ["0"]
    return RawJob([f"p cnf {n} {len(cnf)}"] + cnf, proof, fail)


def top_var_job(seed):
    """Held back: V is 1000000 and the unit (P), P = 1000000 or -1000000, is neither RUP nor RAT,
    (-P w) being in the CNF. The CNF's first line is (x y), and (-x z), (-x -z) make x a failed
    literal that propagation from nothing does not find. RUP lemmas come before (P); the proof
    goes on after it to an empty clause."""
    r, _, vs = lits_of(seed)
    sign = [v if r.random() < .5 else -v for v in vs]
    x, y, z, w, f1, f2 = (sign.pop() for _ in range(6))
    P = 1000000 if r.random() < .5 else -1000000
    filler = sign
    forced = [f1, f2]

    def pads(k):
        return [text(r.sample(c, len(c))) for c in
                ([r.choice(forced)] + [g if r.random() < .5 else -g for g in r.sample(filler, r.randrange(1, 4))]
                 for _ in range(k))]
    rest = [text(c) for c in [[f1], [f2], r.sample([-x, z], 2), r.sample([-x, -z], 2), r.sample([-P, w], 2)]]
    rest += pads(r.randrange(6, 12))
    r.shuffle(rest)
    proof = pads(r.randrange(2, 6)) + [text([P])]
    fail = len(proof)
    proof += pads(r.randrange(1, 4)) + ["0"]
    return RawJob([f"p cnf 1000000 {len(rest) + 1}", text([x, y])] + rest, proof, fail)


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

# a job an archive starts with, by name
FIRST_JOBS = {"sample": [], "hidden": [("run-0907", lambda: top_var_job(9315))]}

# the small jobs each archive ends with, by name
RAT_JOBS = {
    "sample": [("run-5583", lambda: fixed_job(RAT_SAMPLE)),
               ("cnf-2908", lambda: RawJob(*EMPTY_SAMPLE)),
               ("job-6175", lambda: RawJob(*TAB_WIDE_SAMPLE)),
               ("sat-0471", lambda: RawJob(*EMPTY_CNF_SAMPLE)),
               ("run-2219", lambda: RawJob(*STOP_SAMPLE)),
               ("job-7738", lambda: RawJob(*WIDE_RAT_SAMPLE)),
               ("overlap", lambda: fixed_job(OVERLAP_SAMPLE)),
               ("cnf-1187", lambda: RawJob(*MULTI_EMPTY_SAMPLE)),
               ("run-6650", lambda: RawJob(*TOP_VAR_SAMPLE))],
    "hidden": [("cnf-6412", lambda: rat_job(9307)),
               ("run-8843", lambda: edge_job(9308)),
               ("cnf-3055", lambda: empty_cnf_job(9309)),
               ("job-9146", lambda: stop_job(9310, False)),
               ("sat-6620", lambda: stop_job(9311, True)),
               ("run-4417", lambda: wide_rat_job(9312)),
               ("sat-7744", lambda: overlap_job(9313)),
               ("job-2581", lambda: multi_empty_job(9314))],
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
    for name, make in FIRST_JOBS[which]:
        job = make()
        write_job(job, os.path.join(out, name))
        lines.append(f"{name} {job.verdict()}")
    for k in order:
        seed, p, fail, at = spec[k]
        job = Job(seed, p).build(fail, at)
        write_job(job, os.path.join(out, names[k]))
        lines.append(f"{names[k]} {job.verdict()}")
        print(f"{names[k]} seed {seed} vars {job.nv} clauses {len(job.cnf)} "
              f"proof {len(job.proof)} -> {job.verdict()}", file=sys.stderr)
    for name, make in RAT_JOBS[which]:
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
