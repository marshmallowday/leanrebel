# ReBeL status — M06 in progress; M05 accepted

## Resume point

Use the actual remote HEAD of `rebel/m06-carried-iterations-20260923`.
This implementation checkpoint starts from b17501a84ec76c6cd996864144f4a616ac251a00
on the preserved rebel/m06-recursive-envelope-20260923 branch. Main is not changed.
Check this HEAD's M06 targeted proof feedback, ReBeL checks and full CI.
No compilation success is asserted at creation of this checkpoint.

## Current slice

FinDistEventError proves an explicit exceptional-event bound for finite kernels.
PBSCarriedSampling constructs a resolver from the incoming carried joint PBS,
drawing the actual native information-set CFR iteration with t > 0. It plugs
into the existing CarriedResolveStage/executeCarriedResolves runner. Missing
beliefs retain the previous policy; stopped stages retain the existing no-query
rule. The full next-state equation keeps the sampled child paired with the
posterior propagated through that child, not an averaged posterior.

A one-step actual-law comparison against the SAME child's own-reach average
charges 2 * payoffBound * probability(live state with unsupported actual root).
This has no caller-supplied support domination, posterior equality, or local
safety premise. It is a sampling defect estimate, NOT a global recursive
security theorem or proof that the exceptional mass vanishes. Tests and
source-SHA acceptance are the next checkpoint.

## Preserved accepted evidence

Do not redo the fresh-child proof slice at dd66907138cf052a52435d8c31dcb3ecaea5703e.
Its target run 35828662651/job 107075968088 passed target builds, normal/slow
lint and all-declaration axiom checks. See M06-fresh-envelope-validation.md.
The three earlier modules, original source obligations and dependency pins
remain unchanged. The predecessor's full gate status must be read remotely;
old in-progress/cancelled runs are not asserted successful.

## Remaining source obligations

Connect the genuine carried-PBS recursive execution to the parent value oracle
and derive the source-dependent value-drift and exceptional-mass bounds.
History marginal equality does not justify replacing the retained sampled
profile and its posterior in later steps. The generic CarriedResolveStepBounds
is not a discharged theorem. Preserve finite outer T, nonzero prediction and
child errors, off-model unknown-opponent histories and the printed/corrected
Theorem 3 distinction. SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3
remain pending; no complete-M06 or numeric-refinement claim.
