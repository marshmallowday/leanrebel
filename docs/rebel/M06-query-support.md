# M06 actual reference-query reach compatibility

Work branch: `rebel/m06-joint-completion-20260920`.
Parent checkpoint: `289ff1d8d6b0a172a7bdfe39a2e8c690d9aa155e`.
This checkpoint adds CFRDQuerySupport and registers it through the analytic
import closure and the M06 target list. Exact-source validation is pending.

The positive-opponent premise needed by joint completion is now derived for
all supported histories of unilateralReferenceLaw and all its sampled
conditionals. The proof uses the canonical masked chance/own-reach product,
not an assumed support certificate. Early terminal histories are included.

For observations that determine the focal information state, factual support
is equivalent to nonzero original focal own reach on the entire sampled
reference conditional. Thus an absent factual type has zero OWN reach there,
not merely zero factual joint probability. The reverse implication uses the
proved unilateral density and the positive uniform-legal denominator.

The observation can contain additional public or live/terminal data. A public
observation that does not determine private information is intentionally not
covered by the support equivalence. Unsampled reference conditionals are
excluded: their total fallback is not certified as a Bayesian posterior.

Remaining: consume these facts in the constructed joint leaf response for
actual typed kernels, instantiate query typing and PBS Nash from child solves,
and connect recursive child quality to the full finite-T security theorem.
No M06 parent obligation is promoted to verified by this code checkpoint.
