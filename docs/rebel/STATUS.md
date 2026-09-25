# ReBeL status — M06 in progress; M05 accepted

## Current source checkpoint

Work branch: `rebel/m06-value-stability-20260925`.
Base: `c984277c2238e4dd1249ff3ace6fc5444175858a`.
Initial evidence checkpoint: `f71b72cd68b15c2a8b72fdf94aca8502f4fd7fcc`.
Read `M06-value-stability-progress.md` and `M06-value-coupling-coverage.json`.
The previous STATUS is preserved exactly in `STATUS-before-value-coupling.md`.

The new source adds a directed payoff-coupling route to actual-law weighted
fresh re-solving. It derives `childLoss + valueRate + 4*B*referenceRate` from
actual continuation marginals and a one-sided coupling cost. It does not
assume convergence of entire outcome laws. A nonconstant-payoff control has
outcome L1 variation 2 but directed cost 0; direction and incorrect-marginal
negative controls are retained. The noisy finite-parent/two-fresh-solve
consumer discharges referenceRate=0 through the existing source-law theorem.
Its small coupling cost is still an explicit premise, not a Nash consequence.

All three new modules are included in the M06 target list, supplemental normal/
slow lint and transitive axiom audit, and the analytic umbrella. No existing
module or gate is removed. Source compilation and CI inspection are PENDING
at this checkpoint. No `sorry`, custom axiom, warning suppression, dependency
change, local git operation or local GitHub request is introduced.

## Confirmed predecessor evidence

Full CI36093962268, independent ReBeL36093962238 and inventory36093962214
succeeded at c984277c. The downloaded exact-source artifact10846741980 has
ZIP SHA256 d9b2d996fabfd2dd2a644aef1e55313f45c6ad569697c51c299b38157b733894.
Its source-commit.txt matches c984277c. Independent validation artifact10847312931
contains REBEL_AXIOM_AUDIT_PASS declarations=4688 and
REBEL_VALIDATION_PASS modules=239. These are predecessor results, NOT validation
of this new source.

## Remaining M06 obligations

Construct quantitatively small one-sided couplings (or another justified
value bound) for the native solver/late-training queries. The new conditional
bridge does not discharge that obligation. Independent later carried-PBS
re-solving, native first-exit rates and CarriedResolveStepBounds also remain.
Do not identify model PBSs with actual posteriors or independent marginals with
the actual private seed/history law. Keep finite T at zero oracle error.

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 in coverage.json
remain pending. The companion coverage record tracks this conditional slice
without promoting those parent obligations. M06 is not complete; main and
predecessor source branches are not moved. Preserve all earlier failures,
printed/corrected Theorem3 distinctions and proof/numerical boundaries.
