# M04 checkpoint — full-game CFR

## Starting point

Work branch: `rebel/m04`. The preserved starting main commit is
`cf733bd1ffa977681d1197bf80b1dfd7be82ff6e` (accepted M03 documentation).
Its ReBeL checks run `35285842456` and source inventory run `35285842423`
completed successfully. No M04 theorem has been accepted at this checkpoint.
M03's qualified obligations remain qualified; M04 is not a claim that the
entire ReBeL implementation or every paper theorem is verified.

The complete tracked source snapshot was obtained through the GitHub plugin,
from artifact `10523499140` of that same ReBeL run. The ZIP SHA-256 is
`1e99f7d314ccb63bbdf02dcb9ac9cf959c3fbc1952222eaab72913322af04349`.
Local source inspection does not contact GitHub or use local Git. The original
23 files under docs/rebel, including the compressed official inventory and
coverage expansion, are the review scope. Both coverage and inventory
validators pass at the starting snapshot. Document/source review continues.

## Required dependency-closed slices

1. Enumerate every relevant information site in a finite horizon, preserve
   information locality and perfect recall, and construct an actual ordered
   unilateral replacement schedule. Derive the root decomposition rather than
   storing it as a solver certificate or assuming the conclusion.
2. Couple all local regret matchers to one play trace. Realize their payoffs as
   canonical counterfactual action values; establish bounds and a uniform
   finite-iteration whole-policy regret theorem.
3. Construct own-reach weighted behavioral averages, including zero-reach
   fallback, and prove their realization equivalence to privately mixed
   iteration policies. Prove attaining best responses and connect the regret
   bound to the canonical two-player zero-sum approximate Nash predicate.
4. Supply an explicit rational reference solver and a proved refinement to its
   real specification. Fix simultaneous update order, iteration zero, T=0/1,
   and zero positive-regret fallback. Compare nontrivial two-stage executions
   with independent exhaustive best responses and reject coordinate averaging.
5. Compile, audit every transitive axiom, run normal/slow lint and unchanged
   architecture gates, then record the exact source SHA, semantic scope,
   source correspondence and regression evidence in coverage and STATUS.

The imported local matcher and finite-chain telescoping lemmas do not alone
satisfy these requirements. In particular, supplying an unproved hgain field
or a toy one-stage theorem is not completion of M04.

## Layering and compiler loop

Counterfactual solver analysis belongs below the existing Analysis directory;
core ReBeL modules must not import Analysis. Existing canonical histories,
policies, FinDist, reach, utility, deviation and Nash definitions are reused.
New analytic modules must be added to ReBeL's explicit compiler, lint and
transitive-axiom consumers; no current consumer or audit threshold is removed.

A temporary branch-scoped workflow exports the already pinned Lean compiler,
public dependency sources and compiled module closure for offline diagnostics.
It uses read-only checkout with credentials disabled and excludes Git metadata.
Artifact acquisition remains through the GitHub plugin. An offline compiler
result is preliminary; acceptance still requires the actual committed SHA to
pass GitHub Actions. No toolchain or dependency pin is changed by this export.

## Recovery

Read this branch's actual ref, newest commit and associated Actions first.
Resume from saved files rather than rebuilding M03. Commit substantive slices
on this branch; integrate main only after checking current ancestry and final
validation. Do not force-push, reset, use worktrees, or infer completion from
this plan. Update this checkpoint as implementation evidence becomes available.
