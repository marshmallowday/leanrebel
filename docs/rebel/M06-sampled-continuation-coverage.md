# M06 sampled information-set continuation: construction and coverage journal

## Scope and source correspondence

Paper section 5.1 and appendix B distinguish one private uniform completed-CFR
iteration from arithmetic action averaging and fresh per-move resampling.
M06 ROADMAP also requires a seed-carrying execution and a one-sided guarantee
against unknown opponents, separately from a full-profile Nash predicate.
This slice consumes the actual fixed-T information-set child and original-PBS
policy correspondence already in PBSInformationCFR, not a complete-plan learner.

PBSInformationSampling constructs pbsRootCFRIterate/pbsInformationCFRIterate
from cfrPlay and proves uniform/delayed sampling and value identities for the
same cfrIterationLaw used in cfrAveragedProfile. Its native helper permits an
execution horizon different from the training horizon for law equality only.

PBSInformationCarried reuses PrivateIterationState. The selected child iteration
and actual legal history survive every segment; the optional model PBS is
recomputed from the supplied joint root belief and the selected complete
profile at the total elapsed time. Segment composition preserves the entire
joint referee state. The projected history law is the child's computed
own-reach average against every fixed information-local opposing strategy.
Neither actual hidden history nor the opponent's strategy is an input to a
player's information-local action map or to the model-conditioning operation.

PBSInformationSecurity first lifts an ORIGINAL-PBS reference equilibrium against
every new rooted deviation using the reverse decoder. It derives security from
the actual two-player cumulative regret bounds, without a supplied regret or
child-Nash certificate and without doubling the sum-of-regrets allowance.
The native guarantee transfers to the original PBS game and to actual sampled
carried execution. A positive requested error determines a finite count using
the existing pbsInformationBudgetRounds. The reference equilibrium only anchors
the comparison value and is not supplied to the child computation.

## Explicit hypotheses and excluded interpretations

Finite original legal histories and action carriers; canonical information-local
menus with a supplied legal fallback; full original AOH observation; an actual
PublicBelief concentrated on its common public cut; positive completed iteration
count. One-sided security additionally uses zero-sum bounded history payoffs and
a finite segmentation whose total fuel equals the training continuation horizon.
The positive-budget theorem assumes a strictly positive target error.

The root law is the supplied joint PBS, held fixed while varying the opposing
policy. It is not claimed to be the unknown opponent's factual posterior after
an arbitrary outside prefix. No root independence or private marginal product
is assumed. Off-model observations retain None; they do not fabricate a posterior.
Zero-length and terminal segments do not change the selected policy. The
security statement averages the private iteration and says nothing about the
quality of every individual iterate or a last-iterate policy.

This is a fixed child with retained iteration, NOT a theorem equating an
independent solve at a new PBS to the previous child continuation. The original
parent/child recursive value-family and independent re-solving correspondence
remain explicit obligations. Executable rational/numerical refinement is not
claimed. Existing positive prediction error, conditional child loss and outer
finite-T residuals are untouched. Printed/corrected Theorem 3 remain separate.

## Controls and consumers

Examples/PBSInformationSampling instantiates a true live factual posterior, a
randomized unknown opponent, positive uniform index probabilities, both live
strategic rounds with a zero-length segment, no continuation, terminal roots,
a genuinely off-model referee history, and information non-leakage by actual
new iterates. The existing bit-plan reset counterexample is an explicitly
labelled distinct-family negative regression test. Two additional controls
instantiate original-reference security and the constructed positive budget.

All inherited target, umbrella and supplemental auditor entries are retained.
Sampling, carried execution, security and the controls are explicit consumers
of both normal/slow lint and transitive axiom audit. No dependency pins,
workflow gates, allowed axioms or original content-hashed coverage rows change.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 are not marked closed.

## Verification boundary

This journal records compiler candidates until exact-source checks are inspected.
The inherited c4fee1db sampling failure was a missing type argument on
Option.some_injective, repaired at 9d356e4f. The first registered carried
candidate d0f9d4d1 compiled the sampling module but failed because its recursive
self-call redundantly supplied the captured section parameter M. The present
repair changes that call, not the theorem. Further compiler, lint and axiom
results must be read before this slice is accepted. No M06 completion claim.
