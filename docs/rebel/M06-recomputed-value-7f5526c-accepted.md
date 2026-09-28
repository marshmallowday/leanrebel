# Recomputed-value dependency accepted on 7f5526c

Exact source: 7f5526ca40282dd11a42301e5d12cad9ac3eb37e.
This closes the cbda1b3/d9c73f0/7f5526c proof and documentation repair loop.
It does not complete M06 or promote SEARCH-CFRD/SEARCH-ERROR/SAFE-THEOREM3.

| Workflow | Run / job | Result |
| --- | --- | --- |
| CI | [36422271712](https://github.com/marshmallowday/leanrebel/actions/runs/36422271712) / 108927635040 | success |
| ReBeL checks | [36422271598](https://github.com/marshmallowday/leanrebel/actions/runs/36422271598) / 108927633698 | success |
| M06 targeted | [36422271775](https://github.com/marshmallowday/leanrebel/actions/runs/36422271775) / 108927634835 | success |
| Source inventory | [36422271594](https://github.com/marshmallowday/leanrebel/actions/runs/36422271594) / 108927634201 | success |

Each run's head_sha equals the exact source. Complete decoded job logs were
read through the GitHub plugin, including wrapped axiom lists. There are 2275
targeted and 5411 global unique transitive axiom records, and no axiom outside
propext, Classical.choice and Quot.sound. Every required module reports
LINT_PASS: 140 targeted / 281 global. The traced linter suites include normal
and slow checks such as simpNF. Both final VALIDATION_PASS markers are present.

CI full build succeeds with 4307 jobs, lint build with 4077 jobs, and full-library
lint succeeds. All three architecture audits report VERIFIED=1; the source
metrics are LIBRARY_LINES_OVER_100=0 and TRANSPORT_ANALYSIS_SOURCE=0.
ReBeL checks reports RATIONAL_RUNTIME_PASS and 210 Python tests in 7.924s.
Inventory reports 210 tests in 8.261s. These are actual Actions observations,
not local execution or a claim that the GitHub plugin runs Lean.

Artifact metadata: CI10971255582, global10972000332, target10971235298,
source10970192183. The inventory has no artifact. ZIP contents were not read;
complete decoded logs are the evidence.

Reviewed source blobs:
- PBSRecursivePosteriorValue: 8244b3e286ac9feb300be0982c115bcd5f5b780d.
- PBSRecursiveRecomputedValue: 21bdf43f9cf4d69caf07f347bd379b444b2afb00.
- Examples/PBSRecursiveRecomputedValue: d659104c3fe4a303be2ced4d3b765c7180b118ec.

The signed value change uses the two actual computations and one unchanged
unknown opponent. Filtering bounds only the centered posterior residual.
Off model support, sampling-versus-average replacement costs at most twice
the payoff bound times actual unsupported-state mass. Sequence accounting
uses native full-state forward laws, including the retained draw and its saved
MODEL posterior, and covers stage plus late fuel. Missing/stopped branches
preserve the original behavior. The resulting budget is computed, not shown
small. It does not establish rooted-child/fresh-original solver identity.

The three Lean consumers and five Fraction tests retain changed budgets,
correlation, late continuation, gains, zero stages, and a counterexample to
discarding changed-policy cost when posterior laws agree.
The frozen historical ledger and already accepted source journals are unchanged.
New source must receive its own exact-SHA validation.
