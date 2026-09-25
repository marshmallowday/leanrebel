# M06 conditional-value stability checkpoint

## Pinned starting point (2026-09-25)

This work continues `rebel/m06-scalar-checkpoint-20260925` at
`d2cb889b5538bc9429eb47a7a7e32309d0e31bb7`, not the older M05 default branch.
GitHub compare confirms that its two commits after validated source
`5a9fc55e6b944abb16ec7f2e16e80deb0db341f3` change only eight documentation files.

The independent ReBeL run `36113477739` has now completed SUCCESS at SOURCE
`5a9fc55e6b944abb16ec7f2e16e80deb0db341f3`, on
`rebel/m06-scalar-tail-repair-20260925`. Its jobs are source snapshot
`108001998376` and compiler/lint/transitive-axiom checks `108001998664`.
The latter's architecture, ledger, rational runtime, compile/audit/lint and
cleanliness steps all succeeded. This resolves the predecessor STATUS's
pending independent ReBeL check. It is not an exact-SHA test of new code.

Correction to initial checkpoint `c92031f604e6a0d526bcf3e897dd8799371bfa17`:
that note incorrectly attached this run to d2cb889b and listed unrelated job
identities. The actual run and jobs were re-read through the GitHub plugin;
the exact identities immediately above supersede that initial attribution.

## Dependency-closed slice

`PBSConditionalValueStability.lean` proves conditional payoff congruence after
replacing a player's own coordinate when all opposing coordinates agree.
Approximate Nash and remembered-type best-response attainment then give

    p(type) * |u_first(type) - u_second(type)| <= max(error_first, error_second).

This probability-weighted statement is valid at every type, including absent
ones. At a supported type, the corresponding absolute difference is at most
`max(error_first, error_second) / p(type)`. Neither equality of opposing
policies nor positivity of a queried type is silently inferred.

A separate theorem bounds the absolute difference between a solve's own
conditional payoff and its CURRENT opponent's Eq. (1) best-response value.
The budgeted information-set CFR specialization derives approximate Nash
from the actual finite solve. A two-output information-set CFR specialization
likewise derives both Nash premises, but explicitly retains same-opponent
policy equality as a side condition. These results use the canonical
`TypeBeliefSlice`, information-local policies, continuation law and Nash.

## Semantic controls

The positive example executes the existing live HiddenTypes child backend
at root budget 1/8, proving its current-opponent conditional Eq. (1) bound at
every supported full-AOH type. The existing root-slice factory retains the
entire compatible information domain and correlated joint belief.

A new canonical finite type-plan zero-sum game has two equally likely types,
no row decision, and two opposing actions. Every mixed profile is exact Nash
with root payoff zero, but changing the opposing action shifts a conditional
Eq. (1) value by one. This is a finite normal-form necessary-hypothesis control,
not a claimed counterexample to the full ReBeL algorithm. The inherited rare
and absent-type controls are preserved; the new quarter-mass consumer checks
that the conditional gain one exceeds its root error 1/4.

## Validation and remaining obligations

Both new modules are imported by the analytic umbrella, appended to the
existing M06 build targets and explicit exact-leaf audit list, and discovered
by the unchanged repository-wide ReBeL audit. No inherited target, theorem,
negative control, dependency pin, or axiom allowance is removed.

At this implementation checkpoint Lean validation is PENDING exact-source
GitHub Actions. Local source was obtained only from the GitHub plugin's
source artifact. No local git or direct GitHub network access is used.

M06 remains incomplete: these restricted results do not prove equality or
stability of opposing profiles across independent solves, changing-slice
native/late conditional vector rates, native first-exit, independently
re-solved carried-PBS safety, or `CarriedResolveStepBounds`. Root scalar
accuracy and current-opponent optimality do not discharge those obligations.
The original SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3
source obligations are not marked complete or weakened.
