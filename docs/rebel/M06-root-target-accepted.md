# Root information-value target source acceptance

Source: [main paper section 5.1, page 6](https://papers.nips.cc/paper/2020/file/c61f571dbd2fb949d3fe5ae1608dd48b-Paper.pdf).
The searched root stores an information-state value vector from each round's
current strategy and leaf predictions. The subsequent training target averages
these round vectors uniformly. It is not a scalar PBS expectation.

P-CFRD-TARGET is accepted from the unchanged source at
107bbaa5d7017e0dc92a85acfab73b90ac81618d, whose complete same-SHA validation is
recorded in M06-root-memory-107bbaa-accepted.md.

## Mapping

cfrDDepthValueTarget backs up the actual cfrDDepthQuery prediction along the
actual cfrDDepthPlay prefix; terminal and exhausted branches use exact payoff.
The coordinate is a player's information-local root label. pbsRootValueReadout
reads the administrative root snapshot rather than a hidden world or latest
private observation. pbsRootDepthValueTarget instantiates the constructed noisy
finite-child parent, with the extra root chance transition included.

pbsRootValueReadout_law and pbsRootDepthValueTarget_support identify the mask with
the incoming joint PBS's own-type support. pbsRootDepthFullTarget_original
identifies the exact comparator with the original conditional continuation.
pbsRootDepthValueTargetMean_original_error transports the numerical bound through
the actual uniform mean without inverse root mass. The input correlation is
not replaced by a product of marginals. Total absent-label values are explicitly
distinguished from observed training coordinates.

cfrDValueTargetMean_eq_sum/one/succ give the uniform arithmetic and online update.
Examples include a nonconstant two-coordinate vector, a different final-round
value, a real noisy parent and a hidden-state non-leakage control. Fraction
controls reject hidden-state pointwise accuracy, incorrect marginalization,
lost root memory and independently mixed joint-policy evaluation.

## Boundaries

This journal accepts only P-CFRD-TARGET. P-CFRD-AVERAGE remains pending:
its fixed-trace average-policy convergence clause must be accepted separately
from vector arithmetic and finite-budget guarantees. SEARCH-CFRD,
SEARCH-ERROR and SAFE-THEOREM3 are not upgraded.

The new arbitrary-depth training-output modules are additional pending work;
their source is not covered by the 107bbaa success. No claim is made that
averaged targets converge to a particular Nash information-value vector, or
that a learned predictor meets its accuracy contract. Main uniform weighting
does not stand for the supplement's linear weighting or warm-start variant.
