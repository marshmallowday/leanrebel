# M06: constructed depth-limited solving at a carried joint PBS

## Scope

PBSRootDepthCFR installs the actual constructed sampled-value CFR-D parent at
the canonical PBS chance root. A root draw costs one administrative transition;
the original cut and remaining horizons are not conflated. Every round computes
information-set child CFR, completes zero-own-reach queries, and consumes the
sampling expectation plus numerical noise. The state sequence is the same
coupled recurrence as the existing constructed driver.

PBSInformationDepthCFR decodes that output and its actual iterates through
original local AOH. The all-behavioral-deviation Nash bound and uniform private
iteration history law transfer to the original belief game. The explicit
cfrDDepthMeanBudget sum retains numerical error, positive child loss and the
finite outer iteration term. No child Nash, regret or local optimality
certificate is supplied by the caller.

PBSCarriedDepth installs this newly computed depth-limited iteration family
into the pre-existing CarriedPublicResolver and finite memory runner. The
actual hidden history and unknown-opponent policy are not solver arguments.
The full canonical next-state equation keeps each selected iterate paired
with the posterior propagated through that same iterate. Missing beliefs
retain the old profile; zero execution fuel uses the existing stopped branch.
This is not an independently averaged-PBS reset.

## Concrete controls

Examples/PBSCarriedDepth builds a four-outcome supported joint belief before
both strategic rounds of the existing hidden-type protocol. The first solve
searches one strategic round and uses computed children for the remaining
round. Prediction bias1/8 and child tolerance1/4 remain nonzero. Tests cover
all-deviation approximate Nash at arbitrary positive finite outer count,
local hidden-information indistinguishability, actual sampled history laws,
incoming-belief independence from the old family, the complete paired
profile/PBS next-state law, missing beliefs, stopped execution and a finite
two-solve schedule with distinct counts and local cuts.

## Preserved predecessor and failures

The branch starts from80acca7ed5a45463504947bf483b3f5d4f61b8e0. The actual
pre-existing multi-stage source was4bf56ccc8d0f1ae3c7ab5b79487749c454e7469e,
not merely6c541fca. Its line-width violation was fixed in3d1025ba; the exact
M06 run35884139530/job107259831644 compiled FinDistSequentialError and
reported a proof-local letI style error in PBSCarriedRecursion. That was
corrected in80acca7e without altering statements or disabling lint.
Target35885378257/job107264073356 has confirmed its full target build success;
the supplemental audit was still running when this checkpoint was prepared.
The root/decoder implementation was first saved in163f66705f0620735b391f3ac0461f5b5b44d0d8.
Check the current source's own exact-SHA CI, including these new concrete controls.

## Source correspondence and limits

Source Theorem3 / supplement G uses the continuation algorithm's expected
policy in the parent and samples actual iterations during execution. This
checkpoint connects the depth-limited parent's sampling expectation and its
local-AOH decoded iteration family at a supplied PBS, then exposes that same
family to the carried execution. It does not substitute an arbitrary freshly
chosen equilibrium for that algorithm.

The deepest children still use the established full-root information-set CFR
backend. An arbitrary-depth recursive solver, its query/execution coherence,
and unrestricted recursive safety remain to be connected. No premise equates
the model PBS to the unknown opponent's actual posterior. The earlier full-state
history-first comparator remains analysis-only. Exceptional-mass rates and
fresh model-value drift are not silently set to zero.

## Verification

Every new module is in the analytic root, M06 target list and supplemental
normal/slow lint and transitive-axiom audit. Exact-source acceptance remains
pending until the relevant CI completes. SEARCH-FRONTIER, SEARCH-CFRD,
SEARCH-ERROR and SAFE-THEOREM3 stay pending.
