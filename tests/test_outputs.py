"""Grades the two runs tests/test.sh made of the agent's checker.

Each run's standard output is the report; tests/golden/<run>.txt is the report that archive must
get, one "<job> OK" or "<job> FAIL <line>" per job in the order the archive lists its jobs, as the
generator's recipe claims it. tests/golden_ref/<run>.txt is the same report derived a second time,
from the archive's files alone, by solution/independent_check.py, a checker written from the
README's rules that shares no code with the generator or the reference; the first test asserts
the two agree. Every job in both archives exists to make one reading of the README's rules show:
which job carries which rule is written next to its test below. Lines are compared exactly, with
only the line terminator taken off; a missing final newline is accepted.
"""

from pathlib import Path

RUN = Path("/opt/run")
GOLDEN = Path("/tests/golden")
GOLDEN_REF = Path("/tests/golden_ref")
LIMIT_MS = 60_000

# which rule each job isolates (names are the ones the archives list)
SAMPLE = {
    "run-0316": "clean",     # extension RAT lemmas, a variable reused after its clause was deleted,
                             # a clause learned twice with one copy deleted, reasons restated and deleted
    "job-5260": "dropped",   # a block lemma after one of its clauses was deleted
    "job-3127": "unit",      # a chain unit that leans on a deleted unit clause
    "sat-1736": "reason",    # a block lemma whose false literal lost its only reason to a deletion
    "cnf-4008": "pivot",     # an extension clause whose first literal is not its pivot
    "run-5583": "rat",       # a lemma that is RAT with a resolvent RUP but not tautological
    "cnf-2908": "empty",     # the empty clause in the CNF: every addition is RUP
    "job-6175": "tabwide",   # tabs between literals; eight-literal clauses force what the proof needs
    "sat-0471": "nocnf",     # a CNF with no clauses
    "run-2219": "stop",      # steps after an accepted empty clause
    "job-7738": "widerat",   # a RAT resolvent of nine literals
    "overlap": "overlap",    # a RAT resolvent that shares a literal, same sign, with the lemma
}
HIDDEN = {
    "sat-7095": "clean",
    "sat-1350": "dropped",
    "cnf-5219": "unit",
    "sat-2364": "reason",
    "sat-2640": "pivot",
    "sat-4684": "large",     # near the README's size bounds; a reason deleted late
    "cnf-6412": "rat",       # RAT resolvents RUP through propagation; a middle resolvent not RUP
    "run-8843": "edge",      # an empty clause in the CNF, then deleted; tabs; eight-literal clauses
    "cnf-3055": "nocnf",
    "job-9146": "stop",      # the final empty clause is rejected
    "sat-6620": "stoplemma", # a unit lemma is rejected
    "run-4417": "widerat",   # a RAT resolvent of ten or more literals
    "sat-7744": "overlap",   # held back: a RAT resolvent that shares a literal, same sign
}


def lines(path):
    """The file's lines exactly, each with its LF taken off; a missing final LF is accepted."""
    text = path.read_bytes().decode("utf-8", "replace") if path.exists() else ""
    out = text.split("\n")
    if out[-1] == "":
        out.pop()
    return out


def golden(run):
    return lines(GOLDEN / f"{run}.txt")


def report(run):
    return lines(RUN / f"report_{run}.txt")


def job_of(line):
    return line.split(" ", 1)[0]


def finished(run):
    rc, ms = (RUN / f"status_{run}.txt").read_text().split()
    return int(rc), int(ms)


def verdict_of(run, job):
    got = [ln for ln in report(run) if job_of(ln) == job]
    want = [ln for ln in golden(run) if job_of(ln) == job]
    assert len(want) == 1
    return (got[0] if got else None), want[0]


def check_job(run, kind, table):
    job = next(j for j, k in table.items() if k == kind)
    got, want = verdict_of(run, job)
    assert got == want, f"{run} job {job} ({kind}): report says {got!r}, the proof earns {want!r}"


def test_two_references_agree():
    """The recipe's reports and the independent checker's reports are the same, line for line."""
    for run in ("sample", "hidden"):
        assert golden(run) == lines(GOLDEN_REF / f"{run}.txt"), run


def test_build():
    """The collected .hs sources compile with the README's ghc line into bin/proofcheck."""
    assert (RUN / "build_check.txt").read_text().strip() == "ok"


def test_sample_run_ended_in_time():
    """The run against the environment's archive (moved to another address and port, smaller
    pages, 5 requests per connection) ends before the 60 second wall limit."""
    rc, ms = finished("sample")
    assert ms < LIMIT_MS, f"still running at the limit (exit status {rc}, {ms} ms)"


def test_sample_report_lists_every_job_in_archive_order():
    """One line per job, in the order JOBS gives, each '<job> OK' or '<job> FAIL <line>', and
    nothing else."""
    assert [job_of(ln) for ln in report("sample")] == [job_of(ln) for ln in golden("sample")]


def test_sample_clean_proof_is_ok():
    """The clean job needs RAT on the first literal, deletions matched as sets, one copy of a
    twice-learned clause surviving its deletion, and a forced literal surviving the deletion of a
    reason that a unit or a second reason restated."""
    check_job("sample", "clean", SAMPLE)


def test_sample_deleted_clause_stops_counting():
    """A lemma that needs a clause deleted a line earlier is rejected at its line."""
    check_job("sample", "dropped", SAMPLE)


def test_sample_deleted_unit_takes_its_literal():
    """Deleting a unit clause leaves its literal unforced; the unit that leaned on it is rejected."""
    check_job("sample", "unit", SAMPLE)


def test_sample_deleted_reason_takes_its_literal():
    """Deleting the only clause that forced a literal leaves it unforced; the lemma that needed it
    false is rejected."""
    check_job("sample", "reason", SAMPLE)


def test_sample_rat_pivot_is_the_first_literal():
    """A clause that is RAT only on its second literal is rejected."""
    check_job("sample", "pivot", SAMPLE)


def test_sample_rat_resolvent_is_checked_by_rup():
    """A lemma that is not RUP is accepted when its one resolvent on the first literal is RUP
    without being tautological; the empty clause after it is rejected. A resolvent that shares a
    literal, same sign, with the lemma itself is still checked as a set, not rejected for the
    repeat."""
    check_job("sample", "rat", SAMPLE)
    check_job("sample", "overlap", SAMPLE)


def test_sample_empty_clause_and_separators():
    """An empty clause in the CNF makes every addition RUP; tabs separate literals like spaces do,
    and eight-literal clauses count in full."""
    check_job("sample", "empty", SAMPLE)
    check_job("sample", "tabwide", SAMPLE)


def test_sample_no_clauses_empty_clause_then_more_steps_wide_resolvent():
    """A CNF with no clauses; an accepted empty clause does not end the check, the steps after it
    count; a RAT resolvent wider than eight literals is checked in full."""
    for kind in ("nocnf", "stop", "widerat"):
        check_job("sample", kind, SAMPLE)


def test_hidden_run_ended_in_time():
    """The run against the held-back archive, reached by host name, ends before the 60 second
    wall limit within 2 GiB of address space."""
    rc, ms = finished("hidden")
    assert ms < LIMIT_MS, f"still running at the limit (exit status {rc}, {ms} ms)"


def test_hidden_report_lists_every_job_in_archive_order():
    """The held-back report has one line per job in the archive's order and nothing else."""
    assert [job_of(ln) for ln in report("hidden")] == [job_of(ln) for ln in golden("hidden")]


def test_hidden_clean_proof_is_ok():
    """The held-back clean job, other sizes and constants, is OK."""
    check_job("hidden", "clean", HIDDEN)


def test_hidden_deleted_clause_stops_counting():
    """Held back: a lemma that needs a deleted clause is rejected at its line."""
    check_job("hidden", "dropped", HIDDEN)


def test_hidden_deleted_unit_takes_its_literal():
    """Held back: the unit that leaned on a deleted unit clause is rejected at its line."""
    check_job("hidden", "unit", HIDDEN)


def test_hidden_deleted_reason_takes_its_literal():
    """Held back: the lemma that needed a literal whose only reason was deleted is rejected."""
    check_job("hidden", "reason", HIDDEN)


def test_hidden_rat_pivot_is_the_first_literal():
    """Held back: a clause that is RAT only on its second literal is rejected."""
    check_job("hidden", "pivot", HIDDEN)


def test_hidden_rat_resolvents_are_checked_by_rup():
    """Held back: a lemma whose resolvents are RUP only through propagation is accepted, and a unit
    whose middle resolvent of three is not RUP is rejected at its line. A resolvent that shares a
    literal, same sign, with the lemma itself is still accepted as a set."""
    check_job("hidden", "rat", HIDDEN)
    check_job("hidden", "overlap", HIDDEN)


def test_hidden_empty_clause_and_separators():
    """Held back: a lemma accepted only through the CNF's empty clause, the empty clause deleted,
    tab-separated lines and eight-literal clauses, and an empty clause at the end that is not RUP."""
    check_job("hidden", "edge", HIDDEN)


def test_hidden_no_clauses_empty_clause_then_more_steps_wide_resolvent():
    """Held back: a CNF with no clauses; after an accepted empty clause is deleted, a later empty
    clause and a later unit lemma are rejected; a RAT resolvent wider than eight literals."""
    for kind in ("nocnf", "stop", "stoplemma", "widerat"):
        check_job("hidden", kind, HIDDEN)


def test_hidden_large_job():
    """The job near the README's size bounds gets its exact verdict (a reason deleted near the
    end makes a late lemma fail)."""
    check_job("hidden", "large", HIDDEN)
