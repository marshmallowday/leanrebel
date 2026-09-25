# ReBeL status — conditioned-query support elaboration repair; M06 incomplete

## Resume exactly here

Work branch: `rebel/m06-conditioned-query-20260925`; read its actual latest head.
Initial implementation: `45664f4a6c8ea312ba7ba6cc2501cb71ba5fd3de`.
Parser repair: `0a0183233232566ac20527af7c4f37ee70be8945`.
Planning checkpoint: `6089d7916192b72577d5e74cb30f70e2d238d2c0`.
Proof parent: `3cfc5e0cc27b2574f585a8a8763794ba73d05687`.
Main remains `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`; M05 is accepted.
M06 and Theorem 3 are NOT complete. Read M06-conditioned-query-repair.md,
M06-conditioned-query.md and M06-conditioned-query-coverage.json.

## Actual compiler feedback

The initial target failed parsing; the parser was repaired. The next exact
0a01832 target 36153218875 / 108131386873 parsed the density theorem but
rejected mt on a set-subset proof. This checkpoint uses an explicit supported
tag argument to derive absence instead. No theorem or gate is weakened.
Artifact and exact-source hashes are in the repair note. The module and its
downstream consumers still need a successful compile; lint/axiom checks were
skipped in both failed runs. Exact latest-source compilation, 107 supplemental
modules' normal/slow lint and complete axiom sets, all-ReBeL and full CI remain
PENDING. Inspect actual new-head logs before any acceptance.

All 92 Python tests passed on the exact initial source export; coverage,
inventory, retained previous STATUS and dependency pins were checked. This is
not Lean verification. Predecessor 3cfc5e0 targeted and full CI passed, with
actual downloaded logs, but its all-ReBeL remained running at last observation.
Keep earlier e651 native global evidence separate from these new modules.

## Candidate and remaining M06 boundary

The candidate constructs canonical retained-seed/type/history execution and
conditions a genuine positive-mass event. Density and support are derived,
not assumed: Q/P <= 1/eventMass. Native conditional mean error costs the
finite-T bound divided by actual event mass; its weighted form and computed
positive budgets are connected. The comparison opponent is still the SAME
computed average opponent at ORIGINAL compatible full joint-history kernels.

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 stay pending.
Public-carried-PBS identification, quantitative support/first-exit/event rates,
independently changing-opponent/PBS native and late rates, recursive re-solving
safety and CarriedResolveStepBounds remain. Do not assume an event-mass floor,
expose private seeds, discard finite-T residuals or replace test-time safety
with learner convergence.
