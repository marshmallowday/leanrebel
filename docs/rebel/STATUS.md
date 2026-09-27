# ReBeL status — schedule-support compiler repair; M06 incomplete

## Latest resumable branch

Continue `rebel/m06-schedule-support-review-20260927`. This repair descends from
b0e1cb58a4f4371c977c9a38e5b786666cda24f7, retaining its seven finite-schedule
fixtures and completed inherited global review. The original candidate source
370384f660a3c57e8f08e98bcf40e3f7528020bb remains on the preserved source branch
`rebel/m06-schedule-support-20260927`. Both retain 7944888, the initial latest
f3cda937012b9c72e7e03b8aa6b7e9d9176f0093 and all earlier native resolver work.
Main is accepted M05, NOT the latest M06 source. No force push or gate change.

## Actual compiler result and focused repair

The complete log and artifact for 370384 TARGET run 36283825513 /
job 108520661241 show FAILURE, not an ongoing successful build. Stale job
summaries were superseded by the finished compiler output. Artifact 10920246119
was downloaded through the connector and completely inspected: the sole source
diagnostic is PBSCarriedSupport.lean:90:10, incorrect nesting in an additive
monotonicity proof term. No target lint or axiom validation ran.

The repaired blob 18ed758848b0bd84933f50c4fae2e6be85bd5902 changes only that term
to explicit nested add_le_add applications. Definitions, all theorem statements,
three Lean controls, seven Fraction tests and all audit consumers are unchanged.
M06-schedule-support-validation.md and the owning coverage JSON record the
failure, hashes, exact repair and previous observations without hiding them.
Next obtain this repair's exact target SHA/run/job and inspect complete target
compiler, normal/slow lint and transitive-axiom evidence before accepting it.
All repaired-source compiler and audit gates are currently pending.

## Completed inherited evidence: do not repeat

Exact 3dfa TARGET: 1,797 complete unique allowlisted records / 110 module lints.
Exact 3dfa GLOBAL run 36281726986 / job 108514756082: success; artifact
10920070597 completely inspected, 4,962 complete records / 253 module lints,
static VERIFIED=1 and exact-source runtime pass. Full CI 36281726988 /
job 108514874942 independently reports all steps successful. See
M06-resolver-support-global-accepted.md and its owning coverage JSON. Earlier
b833 global evidence remains accepted. None of these validates new source.

## Scope and remaining tasks

The candidate composes native charges under actual full-state prefix laws,
bounding visits and first-hit probability, and specializes to noisy depth-CFR
with a bounded future sampling comparison. The sum may overcount and includes
the last transition; the first-hit law itself observes only stage inputs.
The seven new numerical fixtures (all 127 local tests passed) include independent
path enumeration, 2,187 inhomogeneous three-stage cases, missing/stopped states
and private-model prefix countercontrols. Arithmetic tests are not Lean proofs.

Small primitive leakage, changed-PBS native/late value gaps and source-specific
signed CarriedResolveStepBounds remain open. Keep the same unknown opponent,
joint compatibility, public-event denominators and finite-T residuals.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
M06 is incomplete; learner convergence is not a substitute for test-time safety.
No background monitoring is implied.
