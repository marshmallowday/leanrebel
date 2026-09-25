# ReBeL status — M06 in progress; M05 accepted

## Resume from this evidence checkpoint

Checkpoint branch: `rebel/m06-query-gap-checkpoint-20260925`.
Proof source: `5cf1369cf1e886650a90a4e027347dacf589d50b`, retained on
`rebel/m06-query-gap-20260925`. This checkpoint changes documentation only;
it does not cancel or replace that source branch's independent CI runs.
Main was re-read at `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098` and is
unchanged by this work. M06 is NOT complete.

Read `M06-query-gap-validation.md`, its JSON evidence, and
`M06-query-gap-review.md`. The validation record supersedes the implementation
checkpoint's then-pending targeted-test observations. Keep exact-source
validation separate from this document-only commit and from main integration.

## Completed targeted validation of the new proofs

Source 5cf1369c PASSED targeted run `36125907562`, job `108041849267`:
all declared M06 compilation targets, the complete 100-module exact-leaf
validation, its configured Batteries linters, and transitive axiom audit of
1595 declarations. The two conditional-value modules contribute 12 and 23
audited declarations, including private/generated declarations. The actual
artifact log was downloaded through the GitHub plugin, its hash and embedded
source checked, and all nine new theorem axiom lists inspected. Only propext,
Classical.choice and Quot.sound occur. No gate or allowance was weakened.

The exact plugin-exported source also passed all 83 Python tests, ledger and
inventory structure checks, and the 576-file library line-width scan locally.
Both modules were checked in all four existing consumers: umbrella, M06
targets, explicit exact-leaf audit, and the global audit's discovery. Local
static checks are not represented as a local Lean compiler run.

## Restricted mathematical scope

The fixed-slice current-opponent conditional Eq. (1) gap has an absolute
OWN-law mean bound equal to the root approximate-Nash error. An exactly
dominated query law with density at most C on own support has mean gap at
most C times that error, without dividing by a minimum type mass. Actual
finite-T and budgeted information-set CFR outputs derive their Nash premises.
The density cap is an explicit side condition, not a derived native-sampler
rate. The query law changes; the slice and opposing policies do not.

The live HiddenTypes budget-1/8 solve exercises the actual own law with
density one. A normalized rare-type prior/query pair in the canonical
zero-sum game has root error 1/4 but query error one, with exact density (4,0).
The absent-query control rules out false domination. Earlier changed-opponent,
rare-type and off-path controls and all semantic definitions are retained.

## Integration gates still pending at this checkpoint

At the last inspection on 2026-09-25, independent ReBeL run `36125907531`,
proof job `108041928085`, was still in progress in the global compile/lint/
axiom step. Its architecture, fixtures and rational-runtime steps had passed.
Full-library CI run `36125907627`, job `108041951383`, was still in progress.
Source-inventory run `36125907547` completed successfully. Re-check these
exact-SHA runs before integration; targeted success does not replace them.
No full-CI or M06 acceptance is claimed for this source or this checkpoint.

## Preserved earlier checkpoints

Repair source `fa03b39e497e4d9802d978caab052ce2802ccdc1` on
`rebel/m06-conditional-gap-20260925` removed only two redundant simp tactics
from the exact-Nash control. Its targeted run `36124896554`, job
`108038627933`, completed SUCCESS: 100 linted modules, 1581 audited
declarations. Its independent ReBeL run `36124896574`, job `108038645006`,
was still in progress at the last inspection. The failed predecessor remains
`e58eff73bcff5f8a67ccb1745f49bf9e762ba398`, run `36122926779`, job
`108032492682`; its failure was never attributed to the repaired source.

Initial conditional source: `069bb7e91eab35772670fc6e060d90f42e58ac07`.
Scalar checkpoint: `d2cb889b5538bc9429eb47a7a7e32309d0e31bb7`.
Scalar proof source: `5a9fc55e6b944abb16ec7f2e16e80deb0db341f3`.
Preserve `M06_CONDITIONAL_VALUE_STABILITY.md`, the scalar review, evidence,
full-CI records and associated JSON files, including earlier run-attribution
corrections. Parent success is not a substitute for new-source validation.

## Remaining M06 work

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
Native/late-training conditional vector rates, native query-density/first-exit
control, later independent carried-PBS re-solving and CarriedResolveStepBounds
remain. Preserve actual private seed/history laws, off-path cases and model-
versus-actual beliefs. Keep finite-T residuals when oracle error is zero and
keep the printed and corrected Theorem 3 readings separate. No learner
convergence premise may substitute for test-time safety.
