# DRAT Proof Checker

A SAT solver farm files every UNSAT answer in a proof archive: the CNF it was given and the DRAT proof it wrote. Nothing has ever checked those proofs. The agent writes a forward DRAT checker in Haskell (GHC, using only packages already installed) that reads every job off a TCP archive service (`PROOFS_HOST` / `PROOFS_PORT`). The service pages the data with opaque tokens and closes each connection after a fixed number of requests. For each job, the checker prints whether the proof holds or, if not, the line of the first addition that is neither RUP nor RAT on its first literal. `/app/proofcheck/README.md` specifies the protocol, the formats, the exact acceptance rule and the report line.

## What makes it hard

The semantics are textbook and fully stated:

- The formula is a multiset.
- A deletion removes one copy of a clause named in any literal order.
- Every deletion takes effect.
- RAT is checked on the first literal as written.

The difficulty is doing this exactly at scale. The held-back archive contains a job with 743,665 variables, 818,832 clauses and 1,166,617 proof lines, and a run gets 60 seconds and 2 GiB of address space. The checker must therefore keep the top-level forced assignment between lines and propagate with watched literals.

Three simpler designs all give correct verdicts on the shipped archive in one to three seconds but are killed at the limit on the large job:

| Design | Time at a quarter of the large job's size |
|---|---|
| Re-deriving the top level before every lemma | 408 s |
| Re-deriving after every deletion | 656 s |
| Scanning every clause for RAT candidates | 120 s |

Keeping that assignment is exactly what makes deletions dangerous. Solvers delete satisfied clauses, including clauses that forced a literal, and under the stated semantics the literal then stops being forced unless something else forces it. Three plausible shortcuts each fail:

- **Keep the assignment through such deletions** (drat-trim's default reading). This accepts failing lemmas and gets 3 shipped jobs and 7 held-back jobs wrong.
- **Simply clear the literal.** This gets nearly every job wrong, because solvers restate a reason before deleting it.
- **Skip unit deletions.** This also fails jobs.

The right design tracks a reason per variable and rebuilds the forced assignment only when a reason clause is deleted.

## How it's graded

The verifier runs in a separate container and keeps only the `.hs` files under `src`. It builds them as an unprivileged user with the README's `ghc` line, then runs the binary twice through a seccomp launcher that blocks any `exec`, under a 2 GiB address-space limit and a 60-second kill:

1. The shipped archive (14 jobs) on another address, with 150-line pages and 5 requests per connection.
2. A held-back archive (15 jobs, including the large one), reached by the host name `proofs.archive.internal`, with 5000-line pages and 40 requests per connection. It is generated at image build and must match a SHA-256 manifest.

Every report line must match exactly, in archive order. Each archive carries one job per rule, and the targeted tests cover:

- RAT on the first literal only.
- Multiset deletions and relearned clauses.
- Deleted units and deleted reasons.
- Resolvents treated as sets.
- Empty clauses in the CNF, and steps after an accepted empty clause.
- A CNF with no clauses.
- Tabs as separators.
- Variable 1,000,000.

Expected reports come from the generator's recipe (`tests/golden`). They are cross-checked against a second checker written from the README alone (`solution/independent_check.py`, `tests/golden_ref`), and the first test asserts the two agree.

Per `task.toml`, thirty one-edit variants of the reference all scored 0 through this verifier. They include keeping the assignment through deletions, RUP-only checking, any-literal pivot, a fixed host, no reconnect, and the slow re-derivation designs, which time out on the held-back run only. The reference scored 1.

## Repository layout

- `instruction.md`: the task prompt given to the agent.
- `task.toml`: metadata, difficulty, solution and verification notes, and resource limits.
- `environment/`: the agent's container (`Dockerfile`), the proof archive service (`Dockerfile.archive`, `archive/`), wired together by `docker-compose.yaml`; `app/proofcheck/` holds the spec `README.md`, the stub `src/` and build/run scripts.
- `solution/`: `solve.sh`, the reference Haskell checker (`src/Main.hs`, `src/Archive/Conn.hs`), the seeded archive generator (`generate_archive.py`) and an independent Python checker (`independent_check.py`).
- `tests/`: verifier image and entrypoint (`Dockerfile`, `test.sh`), pytest checks (`test_outputs.py`), the seccomp launcher (`launch.c`), the archive server and generator, the shipped archive and held-back manifest (`data/`), and expected reports (`golden/`, `golden_ref/`).

## Running it

Requires Docker and Harbor (`uv tool install harbor` or `pip install harbor`). From the repo root:

```
harbor run -p . -a oracle
```

This runs the reference solution through the verifier and should score reward 1. To try an agent instead:

```
harbor run -p . -a <agent> -m <model>
```

For example, `-a claude-code`.

---

Task design, data generators, reference solution and verifier by Audrey Pope.
