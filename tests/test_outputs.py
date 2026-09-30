"""Grades the two runs tests/test.sh made of the agent's checker.

Each run's standard output is the report; tests/golden/<run>.txt is the report that archive must
get, one "<job> OK" or "<job> FAIL <line>" per job in the order the archive lists its jobs. Every
job in both archives exists to make one reading of the README's rules show: which job carries
which rule is written next to its test below.
"""

from pathlib import Path

RUN = Path("/opt/run")
GOLDEN = Path("/tests/golden")
LIMIT_MS = 60_000

# which rule each job isolates (names are the ones the archives list)
SAMPLE = {
    "run-0316": "clean",     # extension RAT lemmas, a variable reused after its clause was deleted,
                             # a clause learned twice with one copy deleted, reasons restated and deleted
    "job-5260": "dropped",   # a block lemma after one of its clauses was deleted
    "job-3127": "unit",      # a chain unit that leans on a deleted unit clause
    "sat-1736": "reason",    # a block lemma whose false literal lost its only reason to a deletion
    "cnf-4008": "pivot",     # an extension clause whose first literal is not its pivot
}
HIDDEN = {
    "sat-7095": "clean",
    "sat-1350": "dropped",
    "cnf-5219": "unit",
    "sat-2364": "reason",
    "sat-2640": "pivot",
    "sat-4684": "large",     # near the README's size bounds; a reason deleted late
}


def golden(run):
    rows = [ln.split() for ln in (GOLDEN / f"{run}.txt").read_text().splitlines() if ln.strip()]
    return [(r[0], " ".join(r[1:])) for r in rows]


def report(run):
    """The report as (job, verdict) pairs. Trailing blanks, a missing final newline and blank
    lines are all accepted; anything else on a line is kept and will not match."""
    path = RUN / f"report_{run}.txt"
    text = path.read_bytes().decode("utf-8", "replace") if path.exists() else ""
    out = []
    for ln in text.splitlines():
        words = ln.split()
        if words:
            out.append((words[0], " ".join(words[1:])))
    return out


def finished(run):
    rc, ms = (RUN / f"status_{run}.txt").read_text().split()
    return int(rc), int(ms)


def verdict_of(run, job):
    got = dict(report(run))
    want = dict(golden(run))
    assert job in want
    return got.get(job), want[job]


def check_job(run, kind, table):
    job = next(j for j, k in table.items() if k == kind)
    got, want = verdict_of(run, job)
    assert got == want, f"{run} job {job} ({kind}): report says {got!r}, the proof earns {want!r}"


def test_build():
    """The collected .hs sources compile with the README's ghc line into bin/proofcheck."""
    assert (RUN / "build_check.txt").read_text().strip() == "ok"


def test_sample_run_ended_in_time():
    """The run against the environment's archive (moved to another address and port, smaller
    pages, 6 requests per connection) ends before the 60 second wall limit."""
    rc, ms = finished("sample")
    assert ms < LIMIT_MS - 100, f"still running at the limit (exit status {rc}, {ms} ms)"


def test_sample_report_lists_every_job_in_archive_order():
    """One line per job, in the order JOBS gives, each '<job> OK' or '<job> FAIL <line>', and
    nothing else."""
    assert [j for j, _ in report("sample")] == [j for j, _ in golden("sample")]


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


def test_hidden_run_ended_in_time():
    """The run against the held-back archive, reached by host name, ends before the 60 second
    wall limit within 2 GiB of address space."""
    rc, ms = finished("hidden")
    assert ms < LIMIT_MS - 100, f"still running at the limit (exit status {rc}, {ms} ms)"


def test_hidden_report_lists_every_job_in_archive_order():
    """The held-back report has one line per job in the archive's order and nothing else."""
    assert [j for j, _ in report("hidden")] == [j for j, _ in golden("hidden")]


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


def test_hidden_large_job():
    """The job near the README's size bounds gets its exact verdict (a reason deleted near the
    end makes a late lemma fail)."""
    check_job("hidden", "large", HIDDEN)
