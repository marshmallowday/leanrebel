# ReBeL status — M06 in progress; M05 accepted

## Resume point

Resume from remote HEAD of rebel/m06-reference-transport-20260924.
This adds bounded conditional transport and disappearing-query costs to the
recovered reference-reweight slice. All writes use the GitHub plugin, and main
is not a write target. Its new compiler/lint/axiom acceptance is PENDING.
See M06-reference-transport.md for exact assumptions, definitions and controls.

Predecessor 44a98bb4395db046e1ed602d8dc8fcb8f80df00d is retained on
rebel/m06-reference-reweight-20260924. At this checkpoint its M06 run
35970620266/job107539230730 compiled all targets successfully; supplemental
lint/axiom checks were still running. Independent ReBeL run35970620213/
job107539323485 is separate. Do not promote a whole run from one completed step.
All 126 M06 targets and 88 supplemental modules remain registered unchanged.

## Accepted predecessors

Fresh-chain source46126f37 on rebel/m06-fresh-chain-20260924 and its review
66a8b9ec remain preserved. Independent run35964794487/job107520978527 is now
SUCCESS, including full ReBeL compile/lint/transitive axioms, rational runtime,
independent pure responses and tracked-file cleanliness. The old pending note
is superseded. Target35964794524 and full CI35964794518 also succeeded.
See M06-fresh-chain-validation.md and M06-fresh-chain.md.

Do not redo composition639e3962, recursiona4246792/reviewa5e0700f,
finite budget704e96ff, nestedf9d4def1 or repair751ad17a. Their original branches
and validation records remain intact. Preserve every accepted M05 result.

## Current semantic boundary

The new envelope is childLoss + measuredValueDrift + 2*payoffBound*transport.
Transport uses actual conditional atom differences on jointly supported OLD
queries and an explicit cost when NEW loses an OLD query, never a fabricated
NEW posterior. Its [0,2] bound is not a source-level vanishing rate.
Information-local reweighting gives zero transport, not zero value drift.
The concrete two-solve chain derives local quality from the actual solver.

Remaining: useful state-law-weighted transport/support/first-exit and value-drift
rates, plus CarriedResolveStepBounds for actual repeated independent later PBS
solves. Do not conflate the coherent-plan draw with native iteration sampling,
model PBS with actual unknown-opponent posterior, or finite real specifications
with numerical refinement. Keep positive prediction error, finite T and the
printed/corrected Theorem3 distinction. SEARCH-FRONTIER, SEARCH-CFRD,
SEARCH-ERROR and SAFE-THEOREM3 remain pending; coverage statuses are not promoted.
