# M06 first-exit witness and continuation-error decomposition

## Checkpoint and scope

Resume from the actual HEAD of `rebel/m06-first-exit-20260924`.
The base is `01245b31164eabcb7012e98b36d57b470496dd8e`, whose M06 target and
supplemental normal/slow lint plus transitive-axiom audit passed run35939097445,
job107442786882. Its full repository CI35939097488/job107443102676 and inventory
35939097484/job107442787245 also passed. ReBeL35939097447 was still auditing
at the last inspection; do not infer its result from the other workflows.

The new implementation is checkpointed for exact-SHA compiler validation.
No acceptance is claimed until that new source has its own inspected results.

## Mathematical content

The canonical finite stopping law now returns either none (no exception) or
the entire first exceptional state paired with the unexecuted suffix INCLUDING
the exceptional stage. Forgetting this witness gives exactly the existing
Boolean first-hit law. Kernels equal outside the exceptional event have equal
first-exit witness laws, even if their complete executions differ after a hit.

The complete signed payoff difference equals the native stopping-law expectation
of the two remaining continuation values' signed difference. Its absolute value
is bounded by the expectation of the absolute suffix difference. For globally
bounded observables this computed charge is at most 2*bound*hitProbability.
Unlike the old bound, a harmless exceptional visit need not incur positive loss.

PBSCarriedDepthFirstHit instantiates the identity and charge for the constructed
noisy depth-limited solver. The witness retains all private selected profiles,
the carried model PBS, and the actual history. Finite iteration counts, positive
noise and child tolerance, unknown opponents and arbitrary future kernels remain.
No independent average-PBS reset or model/actual posterior equality is introduced.

## Integration and remaining work

The additions extend existing modules already in the analytic root, M06 targets,
and supplemental normal/slow lint and transitive-axiom audit. No validation gate,
dependency pin, heartbeat limit, or previous theorem/test is removed or weakened.
Concrete first-exit controls and the existing executeCarriedResolves connection
are the next checkpoint, followed by exact-source compilation and audits.

This is a sampling-error localization, not a recursive security proof or a
convergence rate. The suffix values are computed from the native/comparison
kernels, not supplied as a safety assumption. Deriving useful source-level rates
for these values and for model-value drift remains necessary. Arbitrary-depth
child solving and CarriedResolveStepBounds remain unconnected. SEARCH-FRONTIER,
SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 stay pending. Preserve the printed/
corrected Theorem3 distinction and the finite outer-iteration term.
