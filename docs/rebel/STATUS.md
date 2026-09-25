# ReBeL status — conditioned-query parser repair; M06 incomplete

## Resume exactly here

Work branch: `rebel/m06-conditioned-query-20260925`; read its actual latest head.
Initial implementation: `45664f4a6c8ea312ba7ba6cc2501cb71ba5fd3de`.
Planning checkpoint: `6089d7916192b72577d5e74cb30f70e2d238d2c0`.
Proof parent: `3cfc5e0cc27b2574f585a8a8763794ba73d05687` on
`rebel/m06-joint-query-repair-20260925`. Preserve every prior checkpoint.
Main remains `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`; M05 is accepted.
M06 and Theorem 3 are NOT complete. Read M06-conditioned-query-repair.md,
M06-conditioned-query.md and M06-conditioned-query-coverage.json.

## Actual compiler feedback and current repair

Initial target 36152371154 / 108128541644 FAILED at a missing closing
parenthesis in FinDistSelection's density theorem. The repair closes only
that expression, without changing any mathematical premise or conclusion.
No new module has passed full compilation or its axiom/lint checks yet.
Actual artifact, source-export and test-log hashes are recorded in the repair
note. Exact current-head compilation, 107 supplemental modules' normal/slow
lint and complete axiom sets, all-ReBeL and full CI remain PENDING.
All 92 Python tests passed on the exact initial source export, and ledger,
inventory, retained predecessor STATUS and dependency pins were checked.
Those successes are NOT Lean verification.

Predecessor 3cfc5e0 target 36149297405 / 108118391960 is SUCCESS including
104 supplemental modules and 1,626 declaration axiom sets. Its full CI
36149297382 / 108118771741 is also SUCCESS, including architecture and public
lint. Its all-ReBeL 36149297460 / 108118775734 was still running at last check.
Preserve that predecessor evidence and the earlier e651 native global audit;
neither is validation of the new conditioned-query source.

## Candidate scope and remaining M06

The candidate constructs a canonical retained-seed/type/history execution and
conditions an actual positive-mass event. Density and support are derived,
not supplied: Q/P <= 1/eventMass. Native conditional mean error is bounded by
finiteTBound/eventMass and its mass-weighted form, with computed positive
budgets. History marginal is the existing legal averaged runner. The gap's
comparison opponent is still the SAME computed average opponent, at ORIGINAL
compatible full joint-history kernels. Private retained seeds stay private.

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 stay pending.
Public-carried-PBS identification, quantitative support/first-exit/event rates,
independently changing-opponent/PBS native and late rates, recursive re-solving
safety and CarriedResolveStepBounds remain. No positive event-mass floor is
assumed. Keep finite-T residuals even when numerical oracle error is zero.
Learner convergence must not replace independent test-time safety.
