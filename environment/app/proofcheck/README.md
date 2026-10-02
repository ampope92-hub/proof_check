# proofcheck

Every UNSAT answer the solver farm gives goes into the proof archive: the CNF the solver was
handed and the clausal proof (DRAT, text form) it wrote while solving. proofcheck reads each job
off the archive and reports whether its proof stands.

## Talking to the archive

TCP, at `PROOFS_HOST` (a host name or an address) and `PROOFS_PORT`. ASCII, every line ends in
LF.

When a connection opens the archive sends `HELLO proof-archive <n>`. That connection answers n
requests and is closed by the archive right after the n-th answer; open another to carry on.
Deployments set n anywhere from 5 to 200.

- `JOBS` is answered with `JOBS <k>` and then the k job names, one per line. Names are letters,
  digits and `-`, at most 32 characters.
- `READ <job> <part> <token>` reads one page of a job's `cnf` or `proof`. The token is `start` for
  the first page. The answer is `PAGE <m> <next>` followed by the page's m lines. `<next>` is
  `end` on the last page and otherwise the token for the page after. Tokens are opaque strings
  of letters and digits that stay good for as long as the archive runs, on any connection. A
  page has at least one line; how many at most is a deployment setting.
- Anything else gets `ERR <text>` and still counts as a request. Request lines are at most 4096
  bytes.

## The two parts of a job

`cnf` is DIMACS: a first line `p cnf <V> <C>`, then C clause lines, each some nonzero integers
followed by `0`. Literal v is variable v and -v is its negation. There are no comment lines.

`proof` lines are additions, `l1 ... lk 0`, or deletions, `d l1 ... lk 0`. An addition with
k = 0 (the line `0`) adds the empty clause. Every proof's last line adds the empty clause.

In both parts every variable is between 1 and V, no line mentions a variable twice, and no
clause has more than 8 literals.

## What the proof has to satisfy

A proof is checked forward, line by line, against the formula at that line: the CNF's clauses,
plus the additions before that line, less the deletions before it. The formula is a multiset.
The same clause can be in it several times (solvers relearn clauses), and a deletion takes out
one copy. A deletion names its clause by its literals, in any order. Every deletion takes
effect. Up to a proof's first rejected addition, every deletion names a clause that is in the
formula at its line.

Unit propagation: while some clause has all its literals false except one that is unassigned,
that literal becomes true. It reaches a conflict when some clause has every literal false.

A clause R is RUP at a line when unit propagation over the formula at that line, starting from
every literal of R false, reaches a conflict. A clause that holds a literal and its negation is
RUP.

An addition C is accepted when C is RUP at its line, or else when C is not empty and is RAT on
its first literal p (first on the line as written): for every clause D of the formula at that
line that contains -p, the clause C together with the literals of D other than -p is RUP at that
line. With no such D, C is RAT. An accepted addition joins the formula. The check of a proof
stops at its first rejected addition.

## The report

One line per job on standard output, in the order `JOBS` listed them: `<job> OK` when every
addition is accepted, or `<job> FAIL <line>` where line is the number, counting from 1, of the
proof line holding the first rejected addition. Deletion lines count. Nothing else goes to
standard output; standard error is free.

## Build and run

The checker is Haskell, compiled by the GHC 9.0.2 on this box with the packages its global
package database already has (base, array, bytestring, containers, network and the rest of what
`ghc-pkg list` shows). Nothing comes from Cabal or Hackage. `build.sh` is the build the grader
runs:

    ghc -O2 -i/app/proofcheck/src -outputdir <scratch> -o /app/proofcheck/bin/proofcheck /app/proofcheck/src/Main.hs

For grading only the regular `.hs` files under `src` are kept (modules may sit in
subdirectories), and the binary runs from `/app/proofcheck` with `PROOFS_HOST` and `PROOFS_PORT`
set, no arguments and nothing on standard input. The grader stops a run at 60 seconds of wall
clock, caps its address space at 2 GiB and blocks any attempt to exec another program.

An archive the checker is graded on holds at most 15 jobs. A job has at most 1,000,000 variables,
1,000,000 CNF clauses and 1,500,000 proof lines.
