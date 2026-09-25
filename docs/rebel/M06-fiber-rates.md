# M06 supported-fiber quantitative rates — 2026-09-25

## Source checkpoint and validation state

Working branch: `rebel/m06-fiber-rates-20260925`.
Base: `45a59f97b3e02de43cd367c15e8c7f187654e874` on
`rebel/m06-source-rates-repair-20260925`.
All writes and branch operations use the GitHub plugin; main and previous refs
are unchanged. The base repairs the source-rate example failures without
changing any inherited theorem statement. Its targeted run 36082610875,
job 107907611579, has completed successfully, including all declared targets
and the supplemental lint/transitive-axiom validation step. Full CI and the
independent ReBeL gate must be inspected separately.

The additions in THIS checkpoint have not yet been compiled. Inspect CI for
this branch's exact HEAD, not the successful base. Both edited modules already
belong to the analytic root, M06 target list and supplemental audit; no module,
check, dependency pin or axiom allowance is removed or weakened.

## Quantitative bridge

`cfrDFreshValueChange_le_outcomeRate` converts an upper bound on actual
continuation outcome-law L1 variation into a bound on positive OLD-query
value change for bounded payoffs.

`cfrDFreshTransportCharge_le_fiberRates` combines this with relative
unnormalized FIBER differences on supported OLD queries. If the continuation
rate is eta, the reference fiber rate is rho and the payoff bound is B, the
computed live query charge is at most:

    childLoss + B * eta + 4 * B * rho

`cfrDWeightedTransportLoss_le_fiberRates` integrates that uniform bound under
the ACTUAL private parent seed/history law against any fixed unknown opponent.
Perfect recall establishes support under the unilateral reference. The proof
does not replace this joint law by independent marginals or remove an
opponent density from an OLD-model mean. No density upper bound, minimum query
mass, or atomwise absolute continuity is assumed. The source-rate hypotheses
are explicit properties of source probabilities, not an assumed root-security
inequality. A small rate is not inferred from ordinary child Nash quality.

## Controls and constructed consumer

`softJoint` changes only a small part of a query of probability 1/100. Its
relative fiber rate is 1/50 and the proved conditional bound is 1/25, including
when the actual opponent concentrates on that rare query. The NEW-only atom
(true,true) has mass 1/10000 and zero OLD mass. `soft_no_atom_rate` proves that
NO finite atom-relative rate can hold, while the fiber-relative bound does.
This distinguishes the new hypothesis from hidden full-support assumptions.
All previous density, disappearing-query, absent-query and zero-fuel controls
remain intact.

The hidden-type noisy-parent consumer still performs two genuine fresh child
solves with tolerances 1/4 and 1/8, retaining parent bias 1/8 and finite outer T.
`freshChainControl_parent_fiber_zero` derives zero reference transport from
`cfrDFreshInformationChain_referenceLaw` at the SAME cut. Consequently,
`freshChainControl_biased_rate_security` retains only the continuation rate as
an additional source hypothesis; its budget is independent of the unknown
opponent. This is source-law equality, NOT model/actual posterior equality.

## Explicit remaining obligations

This bridge does not prove that eta tends to zero as the fresh solver budget
grows. Independently accurate Nash scalars do not supply that conclusion.
The current two-solve construction uses coherent final-average private draws;
it is not the native iteration sampler, and same-cut source invariance is not
an invariance theorem for independent later carried-PBS re-solving.

Native first-exit rates, later carried-PBS independent re-solving and the
appropriate recursive-security transfer remain open. In particular this file
does not discharge `CarriedResolveStepBounds` for arbitrary fresh Nash choices.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
The printed/corrected Theorem 3 distinction and proof/numerical boundary are
unchanged. Coverage acceptance is not promoted by this candidate checkpoint.
