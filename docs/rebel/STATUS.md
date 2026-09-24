# ReBeL status — M06 in progress; M05 accepted

## Resume point

Use the actual remote HEAD of `rebel/m06-first-hit-recovery-20260924`.
This branch starts at `160569f68d1c9d206a5f7002e2082a0679e5a152` and preserves
all earlier depth-limited and first-hit implementations. Main remains
`6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098` and is not a write target.
Read exact-SHA Actions results before continuing; do not repeat accepted work.

## Recovered failures and current repair

At source `160569f68d1c9d206a5f7002e2082a0679e5a152`, targeted run
35938303113/job107440275573 compiled both FinDistFirstHit and
PBSCarriedDepthFirstHit, then failed in the concrete support proof at
Examples/PBSCarriedDepthSampling.lean:29 with the default 200000-heartbeat limit.
The same `change` expression caused the separate architecture failure:
ReBeL run35938303006/job107440275185 reported TRANSPORT_ANALYSIS_SOURCE=1
against the unchanged expected value 0. Inventory35938302894 succeeded.

The repair unfolds only the named four-point belief and uses support_map's
explicit finite witness. It removes the unnecessary transport expression;
it does not raise heartbeats, change a theorem, remove a test, or weaken a gate.
Its own compiler/lint/axiom acceptance is pending. See M06-first-hit-recovery.md.

## Preserved implementation, do not repeat

The rooted-depth predecessor `964f6d639236d11addf44b79b3dee3fc2ef5d67b` passed
M06 run35888559368/job107274927401, ReBeL35888559003 and inventory35888559143.
Source993635f3 passed target35931852591/job107420379142; the subsequent
54ce64d5 commit wraps three overlong lines without semantic changes.

FinDistFirstHit constructs a Boolean stopping law from canonical FinDist bind.
It charges the probability of the FIRST exceptional visit under native kernels,
not the expected number of visits. PBSCarriedDepthFirstHit connects its
2*observableBound*firstHitProbability bound to the real noisy depth-limited
solver and executeCarriedResolves. The comparator retains native conditional
private profiles paired with their own model PBS; there is no independent
average-PBS reset or assumed model/actual posterior equality.

The concrete controls preserve positive prediction/child errors, distinct
finite counts, supported and reweighted roots, retained full-state coupling,
missing/stopped beliefs, the existing two-stage runner, and late/repeated/absent
events. All modules remain in the analytic root, M06 target list, and
supplemental normal/slow lint and transitive axiom audit.

## Remaining original obligations

A sharper sampling comparison is not recursive security. Arbitrary-depth child
solving is still unconnected; deepest children use full-root CFR. Derive the
source-dependent model-value drift and first-hit/support-defect rates rather
than assuming they vanish. CarriedResolveStepBounds remains undischarged.
Retain finite outer T, positive numerical/child errors, zero-reach completion,
and the printed/corrected Theorem3 distinction.

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
No unrestricted M06 completion or executable numeric-refinement claim. Earlier
source qualifications, source ledgers, and M05 acceptance are unchanged.
