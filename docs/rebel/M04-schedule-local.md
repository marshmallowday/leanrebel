# M04 slice: exhaustive scheduling and total local realization

This is an intermediate proof checkpoint, not acceptance of M04 or a generic
CFR solver. The original five remaining dependency-closed slices in
M04-checkpoint.md still apply, with the progress below.

## Proven declarations and exact scope

`GameTheory/ReBeL/Schedule.lean`, namespace `GameTheory.ReBeL`:
- `ObservationClock` records an information-local trace length. It carries no
  regret, decomposition, convergence or equilibrium conclusion.
- `fullObservationClock` constructs the clock for full AOHs.
- `decisionSiteFintype` derives finite genuine decision sites from the finite
  carrier of every legal history. The ambient full-AOH carrier need not be finite.
- `scheduledSites`, `mem_scheduledSites`, `scheduledSites_nodup`,
  `scheduledSites_ordered`, `scheduledSites_covers`, `scheduledSites_zero`
  enumerate every active nonterminal decision before the horizon, once, in
  nondecreasing depth. Equal-depth sites are not collapsed, and no reference
  profile's support is used. This is a schedule, not yet its root decomposition.

`GameTheory/Analysis/ReBeL/LocalRegret.lean`, same namespace:
- `continuation_withLaw_eq_expect`, `counterfactual_withLaw_eq_expect`,
  `counterfactual_eq_expect_actionUtility`, `actionRegret_eq_sub_expect`.
- `localVector_eq_regretPayoff`, `localVector_withLaw_eq_regretPayoff`.
These use the canonical Protocol runner, counterfactual reach, legal local
choices, continuation value and regret vector. The affine/realization identity
holds at any finite fuel, including zero, under `ActsOnceWhereItMatters` and
finite information fibers; perfect recall discharges the former. Terminal
fiber members contribute a constant continuation value. No `AllNonterminal`
premise is needed. No uniform payoff bound or coupled learner is assumed to
have been constructed by these theorems.

## Nontrivial and hostile examples

The full two-stage simultaneous hidden-type game supplies the examples. Its
full AOH retains the player's own previous action even when states merge.
- Every nonterminal active legal history is covered by the schedule.
- The actual zero-probability second-stage branch remains scheduled for both players.
- Distinct private-information sites at the same depth both remain in the list.
- Horizon zero has no decision sites; zero continuation fuel produces zero regret.
- Arbitrary behavioral profiles and local laws satisfy actual regret realization.
- An actual terminal extension has constant continuation value at every fuel.
These examples do not restrict deviations to the convenient `Plan` subfamily.

## Validation and consumer boundary

Offline development uses only plugin-obtained pinned compiler/dependency
artifacts, without Git or network access from the local runtime. Compiler
4.33.1 and the repository's unchanged pins are verified. Both new public roots
compile; the transitive audit checks 1405 declarations with only `propext`,
`Classical.choice`, `Quot.sound`. The new-module normal/slow environment lint
checks 54 declarations, with no failing messages. All 37 Python tests pass.
These counts describe this development checkpoint, not the future target-SHA
Actions run. Do not use them as a substitute for inspecting that run.

The basic root cannot import Analysis. New analytic modules therefore live
under `GameTheory/Analysis/ReBeL`, with declarations still in `GameTheory.ReBeL`.
`proof_modules()` now includes both public roots and both recursive directories.
The axiom audit selects both defining-module prefixes, including private or
unexpectedly named declarations. The Mathlib dependency fetch uses this same
consumer; complete-library lint imports the analytic root. Regression tests
reject omission of either surface. No old module, linter or axiom gate is removed.

Recovery at `9859ae06e9ea99808690167fc47159f857c3de31` is separately confirmed by
ReBeL run `35295577895`, job `105447322333`, artifact `10527563286`.
ZIP SHA-256: `98e8a2ebfc53ae90c1536df206ff3723d8b321f5befa203264f2965b8eb5a02c`.
Its actual log passes 35 modules and 1367 transitive declarations and includes
`exists_finitePlan_bestResponse` and `exists_pure_bestResponse` with only the
three accepted logical axioms. New scheduling/analytic source is not attributed
to that older validation run.

## Immediate next obligation

Use the actual chronological unilateral policy replacements to derive the
root payoff difference as the sum of counterfactual gains. Handle distinct
same-depth sites explicitly. Then construct the coupled iteration, uniform
bounds, correct averaged behavioral profile, Nash bridge and rational refinement.
Do not turn any of these conclusions into an input certificate merely to call
M04 complete. Keep all M04 parent ledger items pending until their actual full
obligations and target-SHA evidence have been inspected.
