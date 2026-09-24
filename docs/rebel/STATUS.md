# ReBeL status — M06 in progress; M05 accepted

## Resume point

Use the actual remote HEAD of `rebel/m06-depth-recursion-20260924`.
The branch starts at `993635f35761b5bca336a72b8ba74d85ae6b2186`, preserving
the noisy rooted-depth solver and its full-state finite-schedule comparison.
Main remains `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098` and is not a write target.

## Preserved implementation, do not repeat

The rooted-depth predecessor `964f6d639236d11addf44b79b3dee3fc2ef5d67b` passed
M06 run35888559368/job107274927401, ReBeL35888559003 and inventory35888559143.
The later source993635f3 passed target35931852591/job107420379142. Its full
ReBeL run35936622300/job107434978711 found three 101-character expressions.
Commit54ce64d53c578c05c1a3415d47ff3b8e5ade40d5 wraps those expressions only.
Older carried-sampling and corrected proof-local-instance work is preserved;
do not restart from6c541fca,4bf56ccc or3d1025ba.

## Current slice: first-hit sampling bound and concrete controls

FinDistFirstHit constructs a Boolean stopping law from canonical FinDist bind.
It charges the probability of the FIRST exceptional visit under native kernels,
not the expected number of visits. The proposed complete-kernel error bound is
2*observableBound*firstHitProbability. The probability lies in[0,1] and is at
most the earlier native forward-event sum. Kernels may read all private state.

PBSCarriedDepthFirstHit connects this bound to the real noisy depth-limited
solver at each incoming model PBS and to executeCarriedResolves. The comparator
retains native conditional private profiles paired with their own model PBS.
No independent average-PBS reset or model/actual posterior equality is asserted.

Examples/PBSCarriedDepthSampling covers concrete supported/reweighted roots,
full-state coupling, missing/stopped beliefs, distinct finite counts with
positive prediction/child errors, the existing two-stage runner, and hostile
late/repeated/absent event controls. All three new modules are included in the
analytic root, M06 target list, and supplemental normal/slow lint and axiom audit.

The new slice is NOT accepted until its own exact-SHA compiler and audit results
succeed. The core and connection were checkpointed at047906f1 and01f4d5e0.
See M06-depth-recursion.md for recovered failure evidence and the scope boundary.

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
