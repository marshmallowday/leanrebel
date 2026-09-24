# M06 finite depth-budget integration

## Provenance and acceptance boundary

Working branch: rebel/m06-depth-budget-integration-20260924.
Base: 0309f7c022d3911bb3eae6a64790b76a1b0dcc91, whose proof/configuration source
is 487aaedd795d5d3a8b41a608c6a4e13d1967cb1c. Both formerly pending independent
checks on source487aaedd are now confirmed successful: ReBeL run35941683758,
job107450798403, and full CI run35941683736, job107450816152. The ReBeL job
finished compilation/lint/transitive-axiom audit and tracked-file cleanliness;
full CI finished all three architecture phases and full-library lint.
The previously inspected targeted run35941683756 and inventory35941683774
also passed. This closes the first-exit validation checkpoint, not M06.

Repository discovery found an existing divergent budget branch rather than an
absent implementation: rebel/m06-depth-budget-20260924 at2c9bfd52d316032a39a416e7b6934c0fa8093577.
Its two new modules were absent from the first-exit branch and were not named
in its analytic root, targeted list or supplemental auditor. This integration
reuses their exact blobs e517bd078a0d6d09f1afb18d4a6f53b4665c6f3b and
bbb1bf73526dcd3fdeea0f3833def49e377cb057. It deliberately does NOT copy the
older branch's STATUS, first-hit proof or examples over the repaired first-exit
source. Both prior branches are preserved. Main is not a write target.

The new modules are added to all three consumers without removing any prior
module, validation step or test. Their mere presence on the old branch is not
compilation evidence. This checkpoint requires its own exact-SHA CI result.
No dependency, heartbeat, warning policy, architecture gate or axiom whitelist
is changed. All GitHub access and Git writes use the GitHub plugin.

## Mathematical scope

For the actual rooted noisy CFR-D solver, let A and B be its existing summed
error and finite-time coefficients. Its two-player regret budget is bounded by

    A * numericalError + B / sqrt(T) + 2 * childLoss.

For a target tau with A*numericalError+2*childLoss < tau, the implementation
chooses T=floor((abs(B)/(tau-(A*numericalError+2*childLoss)))^2)+1. It proves
that the actual existing solver meets tau against all original behavioral
deviations. It never treats increasing T as eliminating fixed numerical or
child error. An infeasible request remains a total program but has no accuracy
guarantee.

A separate allocation chooses numericalError=tau/(4*(abs(A)+1)) and
childLoss=tau/8. Both are positive for positive tau, and feasibility is proved.
The predictor must still meet the allocated numerical allowance; this is not
a learned-network accuracy proof. A conditional child target uses the actual
joint belief's proved positive mass floor, not an assumed universal floor.

Controls include the canonical four-point hidden-type PBS, a strictly positive
prediction perturbation, quarter-accuracy and conditional accuracy, fixed bias
1/8 and child loss1/4 with a feasible target, nonempty finite iteration counts,
and rejection of an infeasible accuracy guard. Existing tests are unchanged.

## Coverage and remaining work

This is supporting work for SEARCH-CFRD and SEARCH-ERROR (main section5.1,
supplementG/I); all original coverage.json rows remain pending. It does not
prove SAFE-THEOREM3, identify model and actual posteriors, remove support defects,
or discharge CarriedResolveStepBounds. The deepest child still uses full-root
CFR. The next proof task is installing this budgeted depth solver into the
factual-child splice and zero-own-reach completion, followed by structural
recursion over nested child solves. Source-level drift and sampling bounds
remain separate obligations. Preserve finite outer T, positive errors, zero
reach handling, and the printed/corrected Theorem3 distinction.
