# M06 structural recursion: working checkpoint

## Baseline and remote resume point

This branch is `rebel/m06-structural-recursion-20260924`, created from
`d86402210eae417c4114578cff1092fbaa216e86`. Its inherited proof/configuration
source is `f9d4def18411b43fc14c508b079fadb0378bd178`; the two intervening
commits change documentation only. Main is not a write target.

On resumption the exact inherited M06 target run 35947018152/job107467137173
was already accepted, including compilation, normal/slow lint, and transitive
axiom checks (88 modules). Full repository CI35947018228/job107467419037 is
now completed SUCCESS: all three architecture phases, complete public-library
lint and tracked-file cleanliness passed. Inventory35947018259 was accepted.
The independent ReBeL35947018175/job107467137458 remains in progress at this
checkpoint; its result must not be inferred from the other workflows.

## Dependency-closed next slice

Replace the fixed one-extra-level construction by an actual solver structurally
recursive over a finite list of public cut lengths. A node uses its factual
joint PBS, computes positive numerical/child allocations and a nonempty finite
iteration count, then invokes the smaller recursive solver for each child.
The intended base case has zero remaining transitions and uses a legal fallback.
The child Nash bound is to be proved by induction, not supplied by the caller
as a certificate. Preserve complete baseline and unilateral laws, all-query
zero-own-reach completion, independent private iteration semantics, and explicit
administrative chance-root transitions.

This checkpoint contains the work plan, not a new accepted Lean theorem.
Implementation and its exact-SHA validation will be recorded in subsequent
commits. All old modules, examples and audit targets remain in force.

## Scope retained

Structural recursion alone does not establish independent repeated re-solving
security. Source-level model-value drift, quantitative support/first-exit rates,
and CarriedResolveStepBounds remain distinct obligations. The printed Theorem3
and corrected additive finite-T reading remain separate. Do not claim learned
network accuracy, executable real-arithmetic refinement, posterior identity,
or M06 completion. The original SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and
SAFE-THEOREM3 coverage rows remain pending.
