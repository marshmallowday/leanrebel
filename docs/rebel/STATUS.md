# ReBeL status — M04 finite full-game CFR accepted

## Accepted implementation and resume point

M04's ROADMAP deliverable is complete for the stated finite, clocked,
perfect-recall game class. The accepted implementation is
`ee8fdf1d63af8c592d1d2ee4949df385a6341a4f` on `rebel/m04`.
All three required workflows for that exact source succeeded:

| Gate | Run | Job | Result |
|---|---|---|---|
| Full build, library lint, architecture and deep-reachability audits | 35379068655 | 105710826059 | success |
| ReBeL compiler, normal/slow lint, transitive axioms, rational runtime | 35379068914 | 105710649946 | success |
| Source inventory | 35379068803 | 105710657784 | success |

The evidence/bookkeeping commit containing this STATUS must also pass the
normal workflows before main is advanced. Integrate by a non-force fast-forward
of main to the validated documentation commit; do not rebuild or replay earlier
M04 proofs. After interruption, read the actual `main` and `rebel/m04` refs and
exact-SHA CI results first. This file deliberately names the implementation
SHA, not an impossible self-referential documentation SHA.

## What was closed

The finite information-set cover and chronological scheduler are constructed.
Canonical counterfactual values realize the actual simultaneous coupled CFR
updates; bounded game payoffs supply the learner constants. The proved root
identity gives a uniform finite-T regret bound for every complete legal
behavioral deviation. Independent private own-reach averages preserve the
outcome law and give the canonical approximate Nash guarantee.

An attaining pure best response against arbitrary legal behavioral opponents
is proved, not merely characterized. Two given exact zero-sum equilibria have
the same value; positive and non-zero-sum negative controls compile. The exact
rational two-stage solver is connected to the canonical solver for every
iteration, including its averaged output. The positive-T Nash certificate has
no unproved refinement or regret-oracle premise.

The latest repair fixed profile arguments in the value proof and finite-carrier
and conditional elaboration in its regression games. Earlier failed commits
`04e956a`, `0dedfc9`, and `3260052` are not acceptance evidence.

## Evidence and limits

Read [M04.md](M04.md) for the acceptance matrix, assumptions, exact finite-time
constant, rational execution results and scope. [M04-sources.md](M04-sources.md)
records the original CFR dependency and unused smoothing citation.
[M04-compiler-log.txt](M04-compiler-log.txt) retains selected exact build,
82-module lint and 2,189-declaration axiom evidence plus full-CI audit excerpts.
`coverage.json` pins the principal source blobs and preserves M02/M03 evidence.
The acceptance regressions additionally detect lost original obligations,
forged source blobs, failed source SHAs and unsupported verification promotions.

The independent executable check enumerates all 1,024 pure policies per player
and compares actual Lean output for T=0,1,2. The measured NashConv is 2,2,1;
these tests are not claims of exact equilibrium at T=2. Zero samples use the
specified fallback; only positive T receives the averaged Nash certificate.
A whole-game use must choose a horizon covering termination.

The expanded ledger has 3,054 rows: 56 verified, 11 qualified, 406 context
indexed, one empirical runtime record and 2,580 pending. In particular, the
522 official C++ syntax obligations inherited under the M04 parent are still
pending: they are not silently promoted by the Lean finite-game proof. Their
depth-limited, variant and concrete numeric correspondence belongs to the
already documented M06/M08/M09 implementation refinement work. The frozen
original source identities and milestone tags remain intact.

## Next work

Start M05 from the accepted M04 interface: construct PBS equilibrium values
and required minimax/strategy correspondences, then address Theorem 1 with the
recorded source-claim qualifications. Value uniqueness for two given equilibria
is already M04 evidence and must not be confused with M05 existence. ReBeL's
complete framework, learned-leaf search, variant solvers, neural training,
C++/floating-point refinement and full release remain M05–M11 work.
