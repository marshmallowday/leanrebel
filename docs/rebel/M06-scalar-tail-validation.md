# M06 scalar output tails — explicit cutoff and preserved compiler loop

## Source lineage

Initial source ce75519c49043af2b8a640efc82ffa6cfa7e3dca restored the prior
uncommitted candidate on rebel/m06-scalar-stability-20260925.
Its target run36111759855/job107996586904 FAILED. The main PBSValueStability
module compiled, while the example exposed Fin3 disequality simplification,
abbreviation-sensitive simp matching and underspecified expect_map arguments.
The supplemental lint/axiom step was skipped, not passed.

The GitHub-plugin-downloaded failure artifact10853309041 has SHA256
540388194c002971b48cb3301f973b302b2637372e18afaee4a730ad1591d33b.
Exact source artifact10853421894 has SHA256
0521f93a9888a7882e9e846fdcec466bb38195ecd927ecbc50cb370d2600bf4c.
Its embedded commit and TAR hash were checked, and all six implementation,
integration and test files matched the prepared bytes. The old artifact's
failure is retained and no linter is suppressed.

Focused repair737704a90113d99ac135cbd6455ecf2bb7a563e3 supplies explicit Fin3
disequalities, typed value equalities and explicit expectation-map arguments.
Every preexisting theorem statement and consumer remains unchanged.
This tail extension descends from that repair, on a separate branch
rebel/m06-scalar-tail-20260925 so its CI does not cancel the repair branch's CI.

## New mathematical step

Write C=pbsRootCFRBound M roots bound fuel 1. The existing exact factor theorem
identifies the residual at positive t as C*sqrt(t)/t. The existing computed
budget for error e>0 is floor((abs(C)/e)^2)+1.

pbsInformationBudgetRounds_error_of_le proves that EVERY t above this budget
meets residual(t)<=e, not merely the one count chosen by the budget solver.
The proof retains positive denominators, explicitly derives t>0 from the
threshold, and compares squares using sqrt(t)^2=t. It assumes no monotonicity
of strategies or stability of individual native iterates.

pbsInformationCFR_late_value_abs_sub_le sets e=tolerance/2. For any two counts
T,S above the computed cutoff, the actual reach-weighted outputs have
abs(V_T-V_S)<=tolerance. The two legal fallbacks can differ arbitrarily;
belief, horizon and payoff remain fixed. No Nash certificate, value-rate
assumption, exact equilibrium witness or coupling is supplied by the caller.
Both finite-time errors are discharged by the actual solver's existing bound.

The added HiddenTypes consumer pbsValueStability_late_output_control uses the
actual information-set CFR outputs and tolerance1/8. All original positive
budget and sharp negative coupling controls are retained.

## Validation boundary

At source creation this extension still requires exact-SHA compiler, lint and
transitive-axiom validation. All83 Python tests pass locally, including the
new108 exact squared-cutoff checks and the existing6561 scalar game/profile
checks. These are regression diagnostics, not Lean proof evidence.

No additional module is hidden or removed:136 targets and98 supplemental
audit modules remain registered. Only existing new modules are extended.
All workflows, pins, strict axiom allowlists and older examples remain intact.

## Remaining M06 obligations

This closes neither conditional value-vector stability nor native-iteration
sampling. A scalar tail theorem at one PBS does not bound changes under later
carried beliefs. Native first-exit rates, unknown-opponent actual seed/history
transport, later independent re-solving and CarriedResolveStepBounds remain.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 stay pending.
M06 is NOT complete and main is unchanged. See the scoped coverage companion.
