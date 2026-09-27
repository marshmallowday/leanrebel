# ReBeL status — schedule-support abstraction repair; M06 incomplete

## Latest resumable branch

Continue `rebel/m06-schedule-support-review-20260927`. The abstraction correction
is a direct descendant of e1e5a37e26a6d01d2c1cb209d28ca583cfc42054, keeping b0e's
seven finite-schedule fixtures, the 370384 implementation, and all inherited M06
work. The original failed candidate remains preserved on
`rebel/m06-schedule-support-20260927`. Initial latest checkpoint f3c and source
3dfa remain in the ancestry. Main is accepted M05, not the latest M06 branch.

## Actual failures and corrections

370384 TARGET run 36283825513 / job 108520661241 failed at
PBSCarriedSupport.lean:90:10. Complete artifact 10920246119 confirms the additive
monotonicity nesting error; stale in-progress job summaries were superseded.
The e1 correction uses explicit add_le_add nesting without changing statements.

The independent e1 GLOBAL run 36284378049 / job 108522217037 then reported
static architecture FAILURE before compiler setup. Complete artifact 10920495339
shows one analysis transport and one outside-owner representation token where
both fixed budgets are zero. The new nil proof used change and an ENNReal lemma.
This correction replaces them with public FinDist expectation/indicator
nonnegativity, preserving the abstraction boundary rather than editing gates.

Current core blob: ff5bf151d7e8bb146c02a5eeb1749972a77e42a9. No statement, control,
fixture, dependency pin, workflow, audit consumer or gate budget is weakened.
M06-schedule-support-validation.md, M06-schedule-support-architecture.md and the
owning coverage JSON preserve every failed source, run and exact repair.
Next inspect this correction's own compiler, normal/slow lint and complete
transitive-axiom evidence. These checks and the actual global gate are pending.
Neither local lexical checks nor an inherited pass accepts the new source.

## Completed inherited evidence: do not repeat

Exact 3dfa TARGET: 1,797 complete unique allowlisted records / 110 module lints.
Exact 3dfa GLOBAL run 36281726986 / job 108514756082: success; artifact
10920070597 completely inspected, 4,962 complete records / 253 module lints,
static VERIFIED=1 and exact-source runtime pass. Full CI 36281726988 /
job 108514874942 independently reports every step successful. See
M06-resolver-support-global-accepted.md and its owning coverage JSON. Earlier
b833 global evidence remains accepted. None validates new source.

## Proof scope and remaining tasks

The finite-schedule candidate bounds visits and first-hit probability under
actual full-state prefixes, with native noisy depth-CFR and bounded-future
sampling consumers. The sum may overcount and includes the last transition;
first-hit itself observes stage inputs only. Three Lean controls and seven
Fraction tests distinguish these boundaries and wrong private-model weighting.
All 127 local arithmetic fixtures passed; these are not Lean proofs.

Small primitive leakage, changed-PBS native/late value gaps and source-specific
signed CarriedResolveStepBounds remain open. Keep the same unknown opponent,
joint compatibility, public-event denominators and finite-T residuals.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
M06 is incomplete; learner convergence is not a substitute for test-time safety.
No background monitoring is implied.
