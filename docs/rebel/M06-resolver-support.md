# M06 randomized resolver support: candidate implementation

## Source and scope

Work branch: `rebel/m06-resolver-support-20260927`.
Parent: `3d272004909c9e70226aeb430813d3d53f038fdd`, the latest observed
support-rate evidence checkpoint, not main or a branch chosen by name alone.
That parent preserves implementation `b833d49b430ac44c433658f3cc72fd130ff0a87f`
and integrated parent `7326f1e40011b1d4329f09e743491cc7bc7e5746`.

This slice lifts the fixed selected-profile support bound to the existing
`carriedResolvedStep` and `carriedMemoryStep`. The public resolver's actual
finite private draw is integrated without pooling the selected models or
forgetting their coupling with the resulting history. Arbitrary incoming
full-state laws are allowed, including correlated memory/history/model laws.
This is a project dependency toward ROADMAP M06, not paper Theorem 3.

## Declarations and premises

All declarations are in `GameTheory.Analysis.ReBeL.PBSOpponentModelTransport`,
namespace `GameTheory.ReBeL`.

- `carriedStateSupported`: an existing stored posterior contains the actual
  history. Missing beliefs fail this property, unlike the narrower sampling
  exception `pbsCarriedCFRException`.
- `carriedResolvedSupportCharge`: live existing beliefs incur the native draw's
  expected `carriedOpponentSupportCharge` from the actual history point mass.
  A missing live belief costs one. A stopped stage keeps its incoming support
  defect and makes no new public query.
- `carriedResolvedStep_unsupported_le`: derived next full-state failure bound,
  with no support-dominance, equilibrium, or actual/model posterior premise.
- `carriedResolvedSupportCharge_of_supported`: a supported actual history has
  zero incoming support cost, irrespective of its model probability.
- `carriedResolvedSupportCharge_eq_zero_of_support`: zero cost requires explicit
  one-step support inclusion for every history and every profile actually
  sampled by the resolver. This is a sufficient conditional result, not a
  claim that the constructed solver or every unknown opponent satisfies it.
- `carriedMemoryStep_unsupported_le` and
  `carriedMemoryStep_law_unsupported_le`: retain the same event through native
  memory bookkeeping and integrate under actual full-state weights.

The unknown opponent is the same fixed legal policy throughout the transition.
It never updates the stored model. The analysis charge may depend on that
opponent; it is not a public executable stopping rule or an observed quantity.
All new support results omit the unnecessary finite-history-carrier premise.
They still use canonical finite-support laws and finite execution fuel.

## Validation state

Candidate code, not yet compiler-accepted. The existing target list, opt-in
umbrella, normal/slow lint and transitive-axiom module lists already include
this source and its examples. No validation gate, action pin, dependency,
original theorem statement, or original adversarial test is removed.
A real target-SHA build and actual audit records are required before accepting
these additions. The prior b833 target pass is not evidence for new code.

At the first resume check, b833 global run 36277876590, diagnostics job
108504099546, was still in its compiler/lint/axiom step. Its source-snapshot
job 108504099412 had succeeded. The source branch was not advanced or cancelled.
The new implementation has its own workflow identities.

## Remaining obligations

Full finite-schedule first-exit composition and small primitive leakage rates
remain open. This one-transition bound is not substituted for a schedule
probability. Changed-PBS native/late value gaps and the signed
`CarriedResolveStepBounds` still need source-specific discharge. Support
containment alone is not equality of actual and model posteriors or a security
value inequality. Finite-T residuals, joint-type compatibility, actual public
event denominators and original source qualifications are retained.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending;
M06 is incomplete. No learner convergence assumption closes test-time safety.
