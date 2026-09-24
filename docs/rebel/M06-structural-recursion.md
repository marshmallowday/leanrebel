# M06 structural recursion: compositional-child checkpoint

## Baseline and remote resume point

Work branch: `rebel/m06-structural-recursion-20260924`, created from
`d86402210eae417c4114578cff1092fbaa216e86`. Inherited proof/configuration
source: `f9d4def18411b43fc14c508b079fadb0378bd178`. Main is not a write target.
The initial plan checkpoint is845a60bab8f4a9e6f011205a7d1a18629e8a043c.

Inherited M06run35947018152/job107467137173 passed compilation, normal/slow
lint and transitive axiom checks (88 modules). Full repository
CI35947018228/job107467419037 is now completed SUCCESS: all architecture
phases, public-library lint and tracked-file cleanliness passed.
Inventory35947018259 was accepted. Independent ReBeL35947018175/
job107467137458 remains in progress at this inspection.

## First implementation stage: induction interface

CFRDComposedChild.lean defines PBSChildSolve as a function taking the actual
joint public belief and a requested real accuracy, without any proof argument.
PBSChildSolveAccurate is the separate theorem needed of a smaller computation.
The public-child combinator constructs the factual PBS from the CURRENT parent
trunk, calls the function with law.positiveMassFloor*loss, preserves both full
baseline and unilateral history laws, transfers supported private-type budgets,
and applies the existing counterfactual zero-own-reach completion.

The compositional theorems are intentionally conditional on the smaller solver's
accuracy. This stage is not itself the final recursive algorithm. Next discharge
that interface by induction on a finite list of public cut lengths, with a
zero-transition fallback base case, finite allocated parent iterations, and
positive numerical/child allowances. Rooting must continue to account for its
one administrative chance step without counting it as an original transition.

The new module is connected to the analytic root, M06 target list and existing
supplemental normal/slow lint plus transitive public/private axiom audit. All
old entries and the original whitelist remain. No compiler/validation result
has yet been accepted for this new source. Inspect its exact SHA and job logs.

## Scope retained

Structural recursion alone does not establish independent repeated re-solving
security. Source-level model-value drift, quantitative support/first-exit rates,
and CarriedResolveStepBounds remain distinct obligations. The printed Theorem3
and corrected additive finite-T reading remain separate. No learned-network
accuracy, executable real-arithmetic refinement or posterior identity is claimed.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
