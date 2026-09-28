# ReBeL status — Nash replacement batch pending Actions; M06 incomplete

Work branch: rebel/m06-kernel-value-repair-20260927.
Parent and last fully accepted dependency: 7f5526ca40282dd11a42301e5d12cad9ac3eb37e.
Default main: 6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098.
Chat baseline: 9457c198126f3c8b7cb1045bbed2e0053788636f.
GitHub account marshmallowday has admin/push permission.

The recomputed-value repair loop is complete on 7f5526c:
CI36422271712, checks36422271598, target36422271775, inventory36422271594 all passed.
Complete decoded logs contain 2275 targeted/5411 global unique axiom records,
only the permitted three axioms, all 140/281 module lint passes including slow
checks, full build4307/lintbuild4077, all architecture checks, rational runtime,
and 210 Python tests (7.924s/8.261s).
See M06-recomputed-value-7f5526c-accepted.md. This is not new-source validation.

The new coherent batch derives a replacement bound from the actual recursive
solver's Nash theorem. It adds explicit root-law discrepancy and two opposing-
policy execution charges, with primitive finite-fuel rates, rather than assuming
the old/new own policies are close. Under the same model law and computed
opponent the remaining bound is the actual requested solver tolerance.

PBSRecursiveNashAligned requires each solve to cover its stage plus every later
stage and late fuel. This prevents applying a short-horizon Nash theorem to a
longer local replacement. The native envelope, forward budget, signed loss and
initial-security theorem preserve actual private draws, stored posteriors and
unsupported-state penalties. Concrete noisy hidden-type consumers prove a
model-opponent 1/8 bound, native two-stage integration and a horizon-mismatch
negative control. Five Fraction tests cover 729 finite combinations and the
root/opponent/support/horizon boundaries. See M06-nash-transport-batch.md.

Expected new surface: 181 build targets, 143 targeted/284 global modules and
215 Python tests. Existing targets remain; workflows, audit criteria, solver
algorithms and journal-pinned sources are unchanged. Static type review is
recorded through all consumers; actual validation requires new-SHA Actions.

Remaining work is grouped in dependency order: sharpen the actual root,
opponent and support terms into useful fresh-chain rates; identify internal
chance-rooted children with original-game fresh solvers including noise,
posterior, fallback, budget and clock; finish SEARCH-CFRD/SEARCH-ERROR/
SAFE-THEOREM3 source correspondence and acceptance.
The singleton-to-PBS bound can be loose even when aggregate laws agree.
A computed or transported budget is not a small convergence rate.
Stored MODEL posteriors are not the unknown opponent's factual posterior.
Keep hidden correlation, native memory, finite-T/child tolerances and printed
R5 versus corrected claims separate. No network convergence is assumed.

P-CFRD-AVERAGE, P-CFRD-TARGET, SEARCH-FRONTIER/P-SEARCH-SETUP/P-SEARCH-LEAF
remain accepted in unchanged journals. No source row is promoted here.
Frozen coverage.json remains 2fc8cc9ad6607d61bfe397707fb96ac322fbb800.
The previous owner ledger is preserved at
M06-kernel-value-transport-coverage-at-7f5526c.json.

Main agent only; review actual types before each commit. Batch related changes.
Confirm separate same-SHA runs, schedule once about 50 minutes later in JST,
and if still running schedule once about 10 minutes later. Do not cancel runs.
