#!/usr/bin/env python3
"""A second checker, written from the README's rules and nothing else, for the reports in
tests/golden_ref/. It reads an archive's files directly (DIR/jobs.txt, DIR/<job>/formula.cnf,
DIR/<job>/proof.drat) and prints the report:

    python3 independent_check.py DIR > report.txt

It shares no code with the generator or the Haskell reference. The formula is a multiset kept as
a count per distinct clause, with occurrence lists of the clauses present. What the formula
forces at the top level is kept between lines together with the clause that forced each literal;
when the last copy of such a clause is deleted, or the top level is in conflict and a clause goes,
the top level is worked out again from the whole formula. An addition is RUP when assuming its
literals false on top of that and propagating over every present clause reaches a conflict, and
RAT on its first literal when every present clause holding the negation gives a RUP resolvent.
"""
import os
import sys


class Formula:
    def __init__(self):
        self.clauses = []    # id -> tuple of literals
        self.count = []      # id -> copies in the formula
        self.ids = {}        # frozenset of literals -> id
        self.occ = {}        # literal -> set of ids present
        self.n_empty = 0
        self.val = {}        # literal -> True for the true literals, False for the false ones
        self.why = {}        # true literal -> id of the clause that forced it (top level)
        self.reasons = {}    # id -> how many true literals it forced
        self.conflict = False

    # ---- the multiset ----
    def put(self, lits):
        key = frozenset(lits)
        i = self.ids.get(key)
        if i is None:
            i = len(self.clauses)
            self.ids[key] = i
            self.clauses.append(tuple(lits))
            self.count.append(0)
        self.count[i] += 1
        if self.count[i] == 1:
            for l in lits:
                self.occ.setdefault(l, set()).add(i)
            if not lits:
                self.n_empty += 1
        return i

    def take(self, lits):
        i = self.ids.get(frozenset(lits))
        if i is None or self.count[i] == 0:
            raise ValueError("deletion of a clause not in the formula")
        self.count[i] -= 1
        if self.count[i] == 0:
            for l in self.clauses[i]:
                self.occ[l].discard(i)
            if not lits:
                self.n_empty -= 1
            if self.conflict or i in self.reasons:
                self.recompute()

    # ---- propagation ----
    def assign(self, lit, i, trail, top):
        self.val[lit] = True
        self.val[-lit] = False
        trail.append(lit)
        if top:
            self.why[lit] = i
            self.reasons[i] = self.reasons.get(i, 0) + 1

    def propagate(self, trail, start, top):
        """Unit propagation from trail[start:]; True when some clause has every literal false."""
        k = start
        val = self.val
        while k < len(trail):
            f = -trail[k]
            k += 1
            for i in self.occ.get(f, ()):
                free = None
                nfree = 0
                done = False
                for l in self.clauses[i]:
                    t = val.get(l)
                    if t is True:
                        done = True
                        break
                    if t is None:
                        nfree += 1
                        free = l
                        if nfree > 1:
                            break
                if done or nfree > 1:
                    continue
                if nfree == 0:
                    return True
                self.assign(free, i, trail, top)
        return False

    def undo(self, trail, start):
        for l in trail[start:]:
            del self.val[l]
            del self.val[-l]
        del trail[start:]

    def recompute(self):
        self.val, self.why, self.reasons = {}, {}, {}
        self.trail = []
        self.conflict = self.n_empty > 0
        if self.conflict:
            return
        for i, c in enumerate(self.clauses):
            if self.count[i] and len(c) == 1:
                t = self.val.get(c[0])
                if t is False:
                    self.conflict = True
                    return
                if t is None:
                    self.assign(c[0], i, self.trail, True)
        self.conflict = self.propagate(self.trail, 0, True)

    def joined(self, i):
        """Clause i just went from absent to present: extend the top level if it is now unit."""
        if self.conflict:
            return
        free = []
        for l in self.clauses[i]:
            t = self.val.get(l)
            if t is True:
                return
            if t is None:
                free.append(l)
        if not free:
            self.conflict = True
        elif len(free) == 1:
            start = len(self.trail)
            self.assign(free[0], i, self.trail, True)
            self.conflict = self.propagate(self.trail, start, True)

    def rup(self, lits):
        if self.conflict:
            return True
        start = len(self.trail)
        hit = False
        for l in lits:
            t = self.val.get(-l)
            if t is False:          # l is already true, so -l cannot be assumed
                hit = True
                break
            if t is None:
                self.assign(-l, None, self.trail, False)
        if not hit:
            hit = self.propagate(self.trail, start, False)
        self.undo(self.trail, start)
        return hit

    def accepts(self, lits):
        if self.rup(lits):
            return True
        if not lits:
            return False
        p = lits[0]
        for i in tuple(self.occ.get(-p, ())):
            r = list(lits) + [l for l in self.clauses[i] if l != -p]
            if not self.rup(r):
                return False
        return True


def numbers(line):
    w = line.split()
    assert w and w[-1] == "0", line
    return [int(x) for x in w[:-1]]


def check(cnf_path, proof_path):
    f = Formula()
    with open(cnf_path) as fh:
        for line in fh:
            if line.startswith("p") or not line.strip():
                continue
            f.put(numbers(line))
    f.recompute()
    with open(proof_path) as fh:
        for n, line in enumerate(fh, 1):
            if not line.strip():
                continue
            if line.startswith("d"):
                f.take(numbers(line[1:]))
                continue
            lits = numbers(line)
            if not f.accepts(lits):
                return f"FAIL {n}"
            i = f.put(lits)
            if f.count[i] == 1:
                f.joined(i)
    return "OK"


def main():
    d = sys.argv[1]
    with open(os.path.join(d, "jobs.txt")) as fh:
        jobs = [ln.strip() for ln in fh if ln.strip()]
    for job in jobs:
        v = check(os.path.join(d, job, "formula.cnf"), os.path.join(d, job, "proof.drat"))
        print(job, v, flush=True)


if __name__ == "__main__":
    main()
