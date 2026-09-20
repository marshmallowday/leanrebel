# ReBeL status — M06 in progress; M05 accepted

## Active restart

Continue on `rebel/m06-bounded-refresh-20260921`; re-read its remote HEAD.
The validated base is a39599e3b47b1e50ca78d5a6385aa24035d25738. Full repository
CI and full ReBeL validation passed there (173 modules, 3,544 axiom records).
Main stays 6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098. The original STATUS is
preserved in M06-status-before-bounded-refresh.md. No history is rewritten.

## Saved implementation awaiting exact-source verification

CFRDRefreshMix derives complete selected-tail expectation identities and a
2*bound*rate pointwise replacement allowance for a private profile mixture.
CFRDFiniteRefresh computes finite-budget candidates at the actual carried PBS,
retains the CURRENT profile when model support is missing, schedules each solve
for the remaining horizon, and derives all recursive step-comparison premises.
CFRDFiniteRefreshSafety connects this execution to the actual noisy outer
finite-child CFR-D solver, retaining numerical, child, outer finite-time and
refresh terms separately. The additional cost is stageCount*2*bound*rate.
No child Nash, local replacement bound or recursive safety inequality is
assumed. The original-game comparison equilibrium only names its value.

The example module exercises actual nonzero replacement loss, missing beliefs,
a live finite candidate, zero-fuel stopping and a two-stage forward-state bound.
All four modules are registered in the umbrella, target list and supplemental
normal/slow-lint and transitive-axiom audit. Compilation is not yet accepted.
The first core target run 35534241817/job 106140278761 rejected an underspecified
nonnegative scalar in the stopped branch; the proof now types it explicitly.
The algebraic live-case scaling is explicit as well; no claim or gate is weakened.

## Scope and coverage

This is a bounded-refresh variant with a visible replacement penalty, NOT
lossless arbitrary independent equilibrium replacement and NOT the paper's
fixed-T information-set child CFR. Each fresh candidate is a finite adaptive
real-arithmetic normal-form solve. The mixture as a whole is not asserted to
be a child Nash profile. Missing model support is never silently repaired.

SEARCH-CFRD gains a candidate construction of fresh carried-PBS solving and
SEARCH-ERROR gains derived recursive replacement allowances. SEARCH-FRONTIER,
SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 original source parents remain pending.
Inspect exact-source compiler, lint, axiom and semantic evidence before accepting
this slice. The paper-faithful recursive guarantee and original variant remain
separate obligations; no M06 completion or main integration is claimed.
