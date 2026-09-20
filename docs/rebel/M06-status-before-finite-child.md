# ReBeL status — M06 in progress; M05 accepted

## Active implementation restart

Continue on `rebel/m06-finite-plan-rm-20260920`; read its actual remote HEAD.
The starting checkpoint was c16beb4d0325f487a25e902a68c47d7d7db01ca7.
Main remains 6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098, accepted through M05.
M06-status-before-finite-plan.md preserves the preceding STATUS byte-for-byte.
No old source should be replayed and no force update or main integration is intended.

## Current validation boundary

The previous af8b6328 target, supplemental audit and full repository CI passed.
Its full ReBeL run 35508389751 and c16beb4d run 35509163340 ended CANCELLED.
The latter ran for approximately the configured 30-minute limit. Do not mark
these cancelled runs successful. The independent validation-budget branch at
23cebffa6447c332434cfa3ea86aa5073ee0d90f changes only that timeout to 60;
all proof source, action/dependency pins, permissions and audit gates remain.
Inspect its exact-source run 35511013150 / 106078847374 separately.

The new finite-plan source has been saved in stages but is still undergoing
target-SHA compilation and repair. FinDistMassFloor compiled at 9aeb972c.
The mean-regret proof needed explicit definitions and parentheses around the
whole summand; an accidentally mistyped target was restored to its baseline
path. Every original target and test is retained. No new source is accepted
merely because it is registered or because old modules compiled successfully.
The new modules and controls are in the umbrella, target list and supplemental
normal/slow-lint plus transitive-axiom consumer. No verification is bypassed.

## Finite-iteration reference construction

FinitePlanLearning structurally iterates simultaneous regret matching over
complete finite plans. FinitePlanNash uses the canonical expected payoff matrix
and independent average marginals to derive approximate Nash. FinitePlanBudget
computes a positive finite horizon from the derived coefficient and requested
positive error. PBSFinitePlanSolver instantiates the actual finiteBeliefForm,
then realizes legal behavioral strategies with the same error.

FinDistMassFloor derives the minimum positive atom from each particular joint
law. It bounds supported type probabilities for any observation map. One
posterior-specific budget therefore controls all supported types together;
no positive mass floor is assumed uniformly across arbitrary learned PBSs.
The root budget and required iteration count are computed, not supplied as
approximate-Nash or continuation-quality certificates.

This is explicitly a complete-plan NORMAL-FORM reference variant. It is not
the paper's information-set child CFR and not an executable rational or
floating-point implementation. It uses real-valued expected utilities and
may require enormous adaptive horizons at small posterior probabilities.
No exact equilibrium is selected by the finite recurrence. Error zero is
outside the finite positive-budget guarantee. See M06-finite-plan-solver.md.

## Remaining M06 obligations

Complete compiler/lint/axiom and semantic validation of this dependency slice.
Then instantiate these finite solves in the actual public-child splice and
reference-table completion, including zero-factual-mass queries; supported
type Nash alone does not control omitted types. Connect freshly re-solved
carried PBS execution to the outer depth-limited guarantees. Keep this
adaptive normal-form variant distinct from fixed-iteration information-set CFR.

Numerical error, child loss, optional replacement loss, and outer finite-T
error remain distinct. Preserve printed and corrected Theorem 3 statements.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
The original coverage ledger and accepted M00-M05 evidence are unchanged.
