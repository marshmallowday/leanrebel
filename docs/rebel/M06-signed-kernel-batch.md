# M06 joint type kernels and signed value coupling batch

## Continuation and batch boundary

Continue the existing M06 branch from the re-read HEAD
d771e88c97ac1b244812a6d5da99900a61be64ba, whose complete same-SHA validation
is recorded in M06-carried-value-d771e88-accepted.md. Main remains
6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098. Login marshmallowday and repository
admin/push permissions were rechecked through the GitHub plugin.

This combines the related kernel identity, local signed comparison, recursive
composition, security consumer, solver examples and independent controls in
one dependency-ordered implementation. No intermediate lemma commit or
workflow wait was inserted. The next semantic boundary is proving quantitative
rates for the constructed unrestricted solver: structural posterior identities
and measured signed costs do not imply such rates.

## Implemented statements

1. TypeBeliefSlice.ofJointBelief_kernel_law identifies every supported type's
   kernel with conditioning of the supplied complete joint PBS.
   ofJointBelief_kernel_of_absent preserves explicit physical off-path data.
   ofJointBelief_kernel_law_independent proves supported kernels independent
   of that completion. No product-of-marginals replacement is used.

2. resolvedNextState_typeKernel_law connects these kernels to the actual stored
   selected-model posterior. It identifies the two conditioning operations:
   public observation of the chosen continuation, then remembered own type.
   It does NOT identify factual unknown-opponent and model posteriors.

3. conditionalPayoff_ofJointBelief and conditionalPayoff_ofJointBelief_mean
   connect the exact kernels to the canonical value interface and reconstruct
   the original joint PBS continuation payoff. These do not establish that an
   arbitrary independently supplied slice is the solver's recursive slice.

4. carriedReplacementOutcome retains the private draw through stage fuel and
   late continuation. carriedReplacementSignedLoss computes old-minus-new
   expected payoff from the two canonical laws. carriedSignedSequenceLoss
   accumulates it under actual forward full-state laws.

5. executeCarriedResolves_loss_eq_signed proves the exact telescoping identity.
   carriedSignedSequenceLoss_le_executionCharge preserves the earlier
   conservative bound. Negative gains remain in the exact sum.
   privateRecursiveResolve_inherits_signedLoss and
   cfrDDepth_recursive_security_signedLoss connect the sum to the original
   initial security theorem without an assumed local loss certificate.
   Oracle error, child loss and the finite-T term are all retained.

6. carriedReplacementSignedLoss_le_valueCoupling uses an explicit outcome
   coupling: FIRST marginal is the new law, SECOND is the old law. The directed
   cost is the expectation of max(0, old payoff - new payoff).
   carriedReplacementSignedLoss_le_min combines this independently justified
   value cost with the existing execution bound.
   carriedResolveStepBounds_of_valueCoupling constructs the original signed
   stage certificate from those marginal identities and supported pairwise
   payoff bounds. No stage expectation bound is a premise.

These are analysis interfaces. No coupling, actual hidden history, unknown
opponent policy or proof-side type label is exposed as an input to the solver.
A suitable low-cost coupling still needs to be constructed for a general
noisy solver. Taking independent outcomes is not claimed optimal.

## Controls and validation boundary

The same actual noisy two-stage solver now consumes exact signed accounting.
A constant-payoff control gives zero signed loss for the actual native
schedule even though history kernels may change. A selected noisy-iterate
example consumes the recursive type-kernel identification.

Four new Fraction tests cover nine correlated public/type posterior cases,
unreachable type completion, disjoint histories with identical payoff,
coupling marginal identities and direction, diagonal versus independent
couplings, and composition under actual forward weights. The last example
has exact signed loss 2/3, directed cost 1, and a larger history-kernel charge.
These complement, rather than replace, the previous 160 tests.

All 21 new public declarations were checked against the accepted global
declaration-name inventory to avoid another joint-import collision. Changed
Lean line widths are within 100 characters. These are source reviews only:
new Lean compilation, lint, axiom audits and Python execution are pending
the new SHA's Actions. Expected tests increase to 164; build targets remain
156, targeted audit modules 118 and global modules 261. None are removed.
No workflow, audit, dependency, specification or frozen coverage.json changes.

## Remaining original M06 obligations

- Instantiate the identified kernels for every actual recursive value
  comparison, including changes of opponent/model and type domain.
- Derive small quantitative solver-specific source/execution/support rates or
  construct suitable low-cost signed value couplings. Scalar Nash accuracy
  does not imply policy or history-kernel closeness.
- Complete source correspondence and acceptance for SEARCH-FRONTIER,
  SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3. Keep the printed R5 formula
  distinct from a corrected/restricted theorem. Do not drop finite-T error
  at zero oracle error and do not assume learner convergence.

M06 remains incomplete. Future implementation and fixes should again be
batched across related items. After a branch update, confirm same-SHA runs,
schedule this chat once at approximately update plus 50 minutes in JST and
end. If still running at that check, schedule another single check about
10 minutes later. Do not stop workflows or use subagents.
