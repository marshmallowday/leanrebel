# ReBeL status — M06 in progress; M05 accepted

## Resume point

Use the actual remote HEAD of `rebel/m06-first-exit-20260924`.
It preserves source160569f6, support repair01245b31, first-exit theory6be7364c,
concrete controls9165ff11 and Option.isSome normalization9537c4f3.
Main remains `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`; do not write main.
Read exact-SHA Actions results before continuing; do not repeat accepted work.

## Validation state

The base support repair01245b31 passed M06 run35939097445/job107442786882,
including supplemental normal/slow lint and transitive-axiom checks. Full CI
35939097488 and inventory35939097484 also passed. Its independent ReBeL
run35939097447/job107442786889 was still in progress at the last inspection.
Do not promote that pending result to success.

First-exit candidate9165ff11 failed M06 run35940857858/job107448326120:
the uniform-bound proof did not reduce Option.isSome before evaluating the
point-mass probability. Commit9537c4f3 adds that reduction only. Its Math-only
change exposed a missing trigger in the M06 targeted workflow. The current
checkpoint adds GameTheory/Math/Probability/** to that workflow's paths.
No job, target, audit, premise, dependency pin or computational limit is removed.

The new first-exit slice is NOT accepted until its own exact-SHA target and
audits succeed. Inspect the actual current HEAD, not the earlier failed candidate.
See M06-first-exit-diagnostics.md for the observed compiler error and repair.

## Implemented first-exit slice

FinDistFirstHit now constructs a native first-exit law retaining the complete
state and the unexecuted suffix INCLUDING the exceptional stage. Its Boolean
image is the earlier first-hit law. The complete signed payoff discrepancy is
an expectation of suffix discrepancy at these native witnesses. The expected
absolute suffix discrepancy refines 2*observableBound*firstHitProbability.

PBSCarriedDepthFirstHit instantiates this for the constructed noisy depth solver,
preserving selected private profiles, carried model PBS and actual history.
The concrete existing two-stage executeCarriedResolves runner receives the same
computed charge. Controls cover late/absent/repeated events, retained suffixes,
kernel invariance, signed orientation, a harmless future with hit probability1,
and a 1/4-3/4 root with hit probability1/4 and charge1/2. Existing controls remain.
See M06-first-exit.md and M06-first-exit-controls.md.

## Remaining original obligations

The computed real-valued sampling charge depends on the actual kernels and
future observable. It is not an executable learned estimate, a convergence rate,
or a uniform unknown-opponent security certificate. Arbitrary-depth child
solving remains unconnected; deepest children still use full-root CFR.
Source-level model-value drift and useful support-defect/suffix-error rates
remain to be derived. CarriedResolveStepBounds remains undischarged.
Retain finite outer T, positive numerical/child errors, zero-reach completion,
and the printed/corrected Theorem3 distinction.

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
No unrestricted M06 completion or executable numeric-refinement claim. Earlier
source qualifications, source ledgers, and M05 acceptance are unchanged.
