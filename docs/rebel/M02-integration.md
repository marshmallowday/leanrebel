# M02 integration repair and validation provenance

This file records observed results, not an advance declaration of M02 acceptance.
The final accepted implementation SHA and full gate results belong in STATUS.md.

## Recovery checkpoint

The remote `rebel/m02` branch retained all earlier writes through
`d07b17315ab31788dec2c4a87b5d0c2ba47fe0c0`. At recovery, `main` remained at
`8beff57b70f3c5e28fb28724c655207ced881c88`; the work branch was 52 commits ahead
and zero behind. No reset, force-push, or local worktree was used.

At d07b173 the ReBeL workflow `35223557064`, job `105209645083`, succeeded:
17 explicit modules, 1752 build jobs, 963 declarations in the transitive axiom
audit, every module's complete Batteries lint, 23 Python tests, and clean tracked
diff. The allowed axiom set remained propext / Classical.choice / Quot.sound;
individual declarations may depend on subsets. The final success marker was
`REBEL_VALIDATION_PASS modules=17` at 2026-09-17T12:57:18Z.
The source-inventory workflow `35223557023`, job `105209369320`, also succeeded.

Full CI `35223556986`, job `105209398522`, built all 4027 jobs successfully and
passed the reuse signature checks and Phase 1. Phase 2 then correctly rejected
`UNBUCKETED_FILES=16` instead of the required zero. Phase 3 and full public lint
were skipped. Thus the complete d07b173 CI was NOT successful.

## Architecture registration, without loosening an existing gate

The new opt-in root and its 15 submodules did not belong to any pre-existing
transport bucket. The patch adds exactly `GameTheory/ReBeL.lean` and
`GameTheory/ReBeL/` to a separate measured bucket. It does not exclude them from
any global forbidden-pattern, representation-boundary, or line-width scan.
The existing transport regex, every existing expected value, and every deep
reachability probe are unchanged. In particular `UNBUCKETED_FILES` remains zero.

The first explicit ReBeL source baseline is 58 uses, all of which are Lean's
`change` tactic (definitional presentation of a goal or hypothesis). Their count
remains visible under the ORIGINAL transport metric rather than hiding them by
rewriting the metric or moving the files into an experimental directory.
A second gate separately requires zero occurrences of cast, HEq, Eq.ndrec,
Eq.mpr, Eq.rec, and the transport glyph. This source-level count is not a claim
that arbitrary elaborated proof terms contain no equality elimination.

| Module (under GameTheory/ReBeL) | Original-metric count |
|---|---:|
| Adapter | 2 |
| Examples/CommonKnowledge | 1 |
| Examples/HiddenTypes | 9 |
| Examples/HiddenTypesHistories | 7 |
| Examples/HiddenTypesPayoff | 9 |
| Examples/LiarsDice | 6 |
| Examples/LiarsDiceInformation | 3 |
| Examples/LiarsDicePayoff | 6 |
| Examples/ObservedDice | 9 |
| Information | 1 |
| Payoff | 5 |
| Public root, Finite, Knowledge, Response, Examples/ModifiedRPS | 0 |

Preparation run `35242203028`, job `105273203123`, compared the full script patch,
preserved all 42 original literal expected fields, and ran Phase 2 successfully.
The resulting script blob is `87cddf87fc81d7efd0e1ae2bd1f51a5a0b5918d7`.
This one-time baseline construction is not an automatic threshold updater in CI.

## Width repair and rejection controls

The unchanged Phase 3 scan also exposed 12 authored lines of width 101--104.
They were wrapped, not excused by raising the 100-column gate. Preparation run
`35242820995`, job `105275318573`, checked each of the six input file blobs against
the d07b173 tree and asserted that removing whitespace yields identical source.
The complete 12-line patch was printed for review. Both Phase 2 and Phase 3
`-VerifyExpected` runs succeeded. The measured maximum width is 100 and the
number of lines over 100 is zero.

Three isolated negative controls were actually executed on the runner:
an unregistered neighboring module, an added custom axiom, and an extra `change`
use. Each caused a nonzero audit exit; restoring the original checkout restored
success. These mutations were never placed in the prepared source blobs.
These were static audit tests, not Lean compiler checks for the modified source.
The final committed sources must still pass ordinary full CI and ReBeL checks.

The temporary preparation workflow used a repository-local contents-write token
only to create unattached blobs. It did not create commits, move refs, dispatch
other workflows, export credentials, or touch upstream. The workflow is removed
in the commit attaching these reviewed repairs; normal validation remains
read-only. The assistant performs the ordinary commit/ref update separately.

## Scope retained

The additional Response theorem characterizes a best response against arbitrary
fixed legal opponent policies by an attained greatest canonical policy value.
It assumes neither a Nash opponent nor a solver; existence and computation of
best responses are not obtained from this characterization alone.
M03 public beliefs and conditioning, M04 CFR/equilibrium results, later learning,
and the full implementation-refinement obligations remain open.


## Final gate resolution

Implementation 95dbfb2a32175038938315a3da5026deb4287610 subsequently passed all three workflows.
Full CI 35243144402 / 105276473279 built 4027 jobs, passed all Phase 1/2/3 gates including
deep probes, and passed the public lint (3797 build jobs) at 2026-09-17T16:09:33Z.
ReBeL 35243144308 / 105276776415 passed all 17 module builds/lints and the 963-declaration
transitive axiom audit. Source inventory 35243144305 / 105276430059 also succeeded.
Complete job logs were inspected before acceptance. The implementation SHA is not the
later record-only commit. Coverage, STATUS, and M02.md contain the exact scope and counts.
The original 23 Python tests retain an immutable M01-B coverage fixture; a new live-ledger
preservation regression brings the tested total to 24 without weakening the original checks.
