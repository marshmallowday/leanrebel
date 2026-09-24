# M06 structural-recursion recovery — 2026-09-24

## Exact resumption

Branch: `rebel/m06-structural-recursion-20260924`.
Starting source: `6f4cca8321d5d0d1daf143e8805321dd2ff1dcd9`.
The branch HEAD was re-read before writing. Main and predecessor branches are
not write targets. All repository access and commits use the GitHub plugin.

Inspected target run 35950716593, job 107478451359: compilation failed in
CFRDComposedChild.referenceBudget because PublicRootType and its reference
slice require Fintype E.History, whose section declaration occurred only AFTER
this theorem. The missing final declaration was a cascading elaboration error.
The other declared targets compiled; supplemental lint/axiom validation was
skipped after the failure and is not accepted as passed.

## Repair checkpoint

Move only the existing finite-history instance into scope at referenceBudget;
retain the finite-action instance at counterfactual completion. No theorem body,
mathematical conclusion, smaller-solver premise, test, target, dependency pin,
heartbeat, lint gate or axiom whitelist is weakened. The pre-budget law-transfer
interface remains free of the finite-history assumption.

Run the unchanged target workflow and inspect its exact-source diagnostics.
Next construct the parent-node consumer and discharge the smaller-solver
accuracy statement by structural induction; do not call the conditional
combinator itself a recursive implementation.

Coverage parent rows SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3
remain pending. Prior accepted M05 and nested-depth evidence is retained.
Further pending source-level drift, first-exit/support rates and independent
re-solving safety are not discharged by this compiler repair.
