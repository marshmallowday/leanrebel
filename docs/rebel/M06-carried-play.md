# M06 carried private-iteration checkpoint

The preceding checkpoint is 6a5f637e030443b086071db8a05c584824c3d569 on
rebel/m06-recovery. Its targeted proof run 35465760319 and inventory run
35465760284 passed. Full CI and slow-lint/axiom checks were still in progress
at the last read; their results must not be presumed.

CFRDCarriedPlay defines actual referee states retaining the private iteration,
actual history and an optional model PBS. The model conditions the selected
iteration's joint history law, not the unknown opponent's actual law. Equal
public observations yield equal model laws; impossible model observations
have no invented posterior. Policies are still information-local and never
receive the referee's hidden history.

The prefix projection and same-seed continuation equalities prove exact
canonical law preservation across the cut, even at off-model observations.
The existing explicit finite-time private security bound therefore applies
to the carried execution. This is preservation of the selected continuation,
NOT a proof that arbitrary recursively re-solved continuations are safe.
Recursive replacement and adversarial finite-T/seed/averaging controls remain.

The module passes offline pinned Lean 4.33.1 with warnings as errors and is
included explicitly in both umbrella and targeted roots. The eleven targets
and inventory structure check pass locally. No coverage row is promoted and
M06 is not marked complete. All remote writes use the GitHub connector.
