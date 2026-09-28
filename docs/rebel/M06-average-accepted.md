# P-CFRD-AVERAGE source review

The obligation has two parts: uniform averaging of iterative root value
vectors, and convergence of the average policy rather than the last iterate.
[Main paper, p6 section 5.1](https://papers.nips.cc/paper/2020/file/c61f571dbd2fb949d3fe5ae1608dd48b-Paper.pdf)
is read with exact continuation values for the vanishing-error statement;
fixed approximation error leaves a residual bound. The main uniform scheme
is separate from the supplemental linear weighting and warm-start algorithm.

## Implementation correspondence

CFRDValueTarget.cfrDValueTargetMean_eq_sum computes exactly the uniform vector
mean. Its online recurrence and same-round error theorem preserve the actual
noisy trace. CFRDValueTargetMemory identifies supported coordinates with the
original correlated PBS continuation. These sources are unchanged from the
root-target acceptance and were audited again at ba26c02.

CFRDAverageLimit.cfrDConstructedExactAverage_converges quantifies epsilon, a
positive threshold, and EVERY later count of one fixed oracle/learning trace.
The oracle's factual child equilibria and zero-own-reach completion are
constructed internally. The conclusion is IsNash with epsilon error against
all behavioral deviations. No accuracy certificate equal to that conclusion
is an input. This ideal real-valued backend is noncomputable.

CFRDAverageLimit.cfrDInformationAverage_after and
PBSAverageLimit.pbsRecursiveParentAverage_after retain the numerical and
finite-child error floor. The actual recursive tail and budgets are fixed as
the outer iteration count varies; the allocated-count identity recovers the
existing recursive solver. Increasing only that count does not remove fixed
prediction or child errors. The exact driver and this finite driver are not
silently interchanged.

This is convergence in Nash error, not convergence to a designated strategy
profile or convergence of the final iterate. The value-vector arithmetic
does not establish convergence of targets to Nash information values, and
no network-learning convergence is assumed. Main policy averaging is the
existing own-reach realization-equivalent average, not independent uniform
averaging of joint policies at every information state.

## Evidence and remaining scope

M06-average-limit-ba26c02-accepted.md records successful exact-SHA build,
normal/slow lint, all 2130/5271 axiom records and 190 Python tests. Journal
M06-average.json appends verified evidence for P-CFRD-AVERAGE only, pinning
exact source blobs. No implementation source is changed by that acceptance.

SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 still require their broader
integration and source review. Fresh recursive re-solving against an unknown
opponent does not follow from a local Nash-error limit. Printed R5 remains
separate from corrected additive finite-time statements.
