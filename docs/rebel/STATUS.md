# ReBeL status — query-cost proof repair pending Actions; M06 incomplete

Work branch: rebel/m06-kernel-value-repair-20260927.
Repair parent: fb27d899a6f74359cdb28d1bed9790f16934d6cf.
Accepted dependency: f51ac5a306943bcaf4203a2b5e564b3f3f307d76.
Default main: 6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098.
Chat baseline: 9457c198126f3c8b7cb1045bbed2e0053788636f.
Authenticated account marshmallowday has admin/push permission.

The fb27d899 candidate failed in all three compiler jobs with the same
unclosed Option.isSome equality and unused simp argument. Both proof
expressions are repaired together; definitions and signatures are unchanged.
Checks passed static2metrics0, rational runtime and230tests10.193s;
inventory passed230tests10.535s. Full build/lint/axioms remain unaccepted.
See M06-query-cost-fb27d899-failure.md for complete diagnostics, metadata
and dependency-to-example static type review. New-SHA Actions are required.

The a0892dcb/f51ac5a grouped-proof repair loop is complete.
CI36481429715, checks36481429781, target36481429659 and inventory36481429515
all succeeded at f51ac5a. Complete logs show2390 targeted/5526 global
unique axiom records, only the permitted3 axioms, all148/289 configured
module lint passes and final markers, full build4315/lintbuild4085,
architecture3VERIFIED, static2metrics0, rational runtime and225tests
(checks8.119s/inventory10.412s). See M06-grouped-security-f51ac5a-accepted.md.
Artifact metadata was read; ZIPs were not. These results do not validate
the new query-cost source.

The new integrated batch derives zero exact native signed loss when no
fresh query occurs (stopped or missing PBS), then payoff interval width
times actual fresh-query probability. Unsupported hidden histories WITH
a saved PBS still count. List induction accumulates expected query visits
under the unchanged native full-state law, retaining the same private
draw through stage+late and all saved-model correlations.

The actual finite sampled noisy parent supplies initial security.
cfrDRecursiveQuery_security keeps its prediction error, finite-T term and
2*child loss, adding payoff diameter times actual query visits.
cfrDRecursiveQuery_capped_security takes the smaller complete-chain bound
from this and the accepted grouped budget. No support term is silently
deleted: the second bound directly covers unsupported actual queries.
It requires no model/factual posterior equality or opponent agreement.

Concrete hidden-type consumers use bias1/8, childloss1/4, bound2 and
interval[-2,2], with parentcut1/fresh[1,1]/stage1/late1 and
parentcut2/fresh[1]/stage1/late0 (both total horizon3).
Zero fuel with late2 and arbitrary saved state has zero signed loss.
Five independent Fraction controls cover rare query tightness, shifted
intervals, inactive cases, unsupported queries, native joint forward
visits, retained late draws, both global min branches and parent terms.
They are not actual CFR executions.

See M06-query-cost-batch.md for full derivation, static type review,
dependency-ordered remaining groups and the mathematical batch boundary.
Expected surface:190 build targets,152 targeted/292 global modules,
230 Python tests. New-SHA Actions are required. Existing solver definitions,
workflow triggers, heartbeat limits, audit standards and tests are preserved.

Remaining: derive useful solver-specific conditional-root/opponent/support
rates, identify internal chance-rooted child with fresh original computation
including posterior/noise/fallback/budget/clock, complete recursive small-rate
safety and SEARCH-CFRD/SEARCH-ERROR/SAFE-THEOREM3 acceptance. Query visits
can exceed1 and need not decrease with search T. The new cap is not a
vanishing-rate theorem. No prior reset or Nash-to-policy-closeness inference.

Existing P-CFRD-AVERAGE/P-CFRD-TARGET and SEARCH-FRONTIER/
P-SEARCH-SETUP/P-SEARCH-LEAF acceptance journals and pins are unchanged.
No source obligation is promoted. Frozen coverage.json retains
2fc8cc9ad6607d61bfe397707fb96ac322fbb800. Previous owner ledger is preserved
at M06-kernel-value-transport-coverage-at-f51ac5a.json with original blob
1ba4c1f6080887a1ba4cc21d6ac9c6a89a999375.

Main agent only. Review types through all consumers before committing,
batch related changes and fixes, confirm separate same-SHA runs, then
schedule one follow-up about50minutes after push in JST. If still running,
check once and defer about10minutes. Never cancel active workflows.
Full M06 remains incomplete.
