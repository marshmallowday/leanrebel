# M06: constructed depth-limited solving at a carried joint PBS

## Scope of this checkpoint

PBSRootDepthCFR installs the actual constructed sampled-value CFR-D parent at
the existing canonical PBS chance root. A root draw costs one administrative
transition; the original cut and remaining horizons are not conflated.
Every round computes information-set child CFR, completes zero-own-reach
queries, and consumes the resulting sampling expectation plus numerical noise.
The parent state sequence is the same coupled recurrence as the existing
constructed driver, not an independent strategy sequence.

PBSInformationDepthCFR decodes this output and its actual iterates through
original local AOH. The root's all-behavioral-deviation Nash guarantee and
uniform private-iteration history law transfer to the original belief game.
The explicit cfrDDepthMeanBudget sum retains numerical error, positive child
loss and the finite outer iteration term. No child Nash, regret or local
optimality certificate is supplied by the caller.

## Relation to the previous checkpoint

The branch starts from80acca7ed5a45463504947bf483b3f5d4f61b8e0. The actual
pre-existing multi-stage source was4bf56ccc8d0f1ae3c7ab5b79487749c454e7469e,
not merely6c541fca. Its line-width violation was fixed in3d1025ba; the exact
M06 run35884139530/job107259831644 then compiled FinDistSequentialError and
reported only a proof-local letI style error in PBSCarriedRecursion. The latter
was corrected in80acca7e without changing the statements or disabling lint.
Check that commit's own CI before calling the finite-schedule slice accepted.

## Source correspondence and limits

Source Theorem3 / supplement G uses the continuation algorithm's expected
policy in the parent and samples actual iterations during execution. This
checkpoint connects the depth-limited parent's sampling expectation and its
local-AOH decoded iteration family at a supplied PBS. It does not substitute
an arbitrary freshly chosen equilibrium for that algorithm.

The deepest children still use the established full-root information-set CFR
backend. An arbitrary-depth recursive solver, its query/execution coherence,
and the unrestricted recursive safety proof remain to be connected. There
is no assumption identifying the model PBS with the unknown opponent's actual
posterior. The earlier full-state history-first comparator remains analysis-only.
Exceptional-mass rates and fresh model-value drift are not silently set to zero.

## Verification

The new modules are in the analytic root, M06 target list and supplemental
normal/slow lint and transitive-axiom audit. Exact-source compiler acceptance
and concrete nonzero-error tests remain to be recorded after the current CI.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 stay pending.
