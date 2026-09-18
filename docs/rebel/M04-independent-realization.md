# M04 independent-seed realization development checkpoint

## Inspected compiler progress

ReBeL run 35310149111, job 105490322473 at
8138d5540ac61b660262008b251bbec6adfc5424 compiled RegretMatching, CFRTrace,
PayoffBounds, WeightedAverage and OwnReachAverage. Static gates and 37 Python
regressions passed. RootRegretBounds then reported two isolated issues: unused
player instances on the own-reach invariance helper, and a wrong name for the
existing positivePart_le_infDist theorem. This checkpoint corrects those exact
issues; no mathematical premise or audit gate is weakened.

## New source awaiting its own validation

OutcomeReach derives a terminal-aware probability mask: a root run assigns a
history its own-depth reach exactly when it is at the requested cut or already
terminal, and assigns zero to unfinished prefixes or overlong histories.
Consequently equal own-reach functions imply equal complete history laws.
IndependentRealization factors expectations under independent private seed
vectors and connects the own-reach weighted behavioral profile to the canonical
run with one privately selected iteration per player. A shared iteration is not
substituted. Every payoff observable and every finite horizon is quantified.

The compiler success above is not an assertion that the new outcome/seed
sources or all root bounds already passed. They remain in the public analytic
root and full recursive compiler/lint/transitive-axiom consumer. M04 still
requires canonical two-player zero-sum Nash, an executable rational solver and
real refinement, hostile two-stage examples and independent best-response
checks, followed by same-source validation and coverage/STATUS updates.
