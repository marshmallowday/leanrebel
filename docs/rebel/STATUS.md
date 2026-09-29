# ReBeL status — rooted saved-query let reduction repair pending Actions; M06 incomplete

Branch: rebel/m06-kernel-value-repair-20260927.
Accepted baseline: 3f09be2d2b6bbb5e222e6b189f5bc409362ad148.
Default main:6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098.
Chat baseline:9457c198126f3c8b7cb1045bbed2e0053788636f.

Exact 3f09be2 passed CI36524194641, checks36524194648,
target36524194642 and inventory36524194628. Complete decoded logs contain
2489/5623 unique targeted/global axiom records with only the3 permitted axioms.
All161/301 lint modules matched the exact registered selection sets and final
markers. Full build4328/lintbuild4098, architecture3VERIFIED, static2metrics0,
rational runtime and245tests (checks9.410s/inventory6.268s) passed.
See M06-rooted-child-decode-3f09be2-accepted.md. Artifact metadata was read;
ZIP contents were not. This closes the fee60dd/3246e17/3f09be2 repair loop,
but does not validate the new source.

Candidate1bc8827 failed all three compiler jobs at PBSRootStoredValue:140.
The returned common-kernel estimate retained local let binders, preventing
abs_sub_comm from finding its target. This repair inserts dsimp only at error
before the rewrite; definitions, signatures and other proofs are unchanged.
Checks passed static2metrics0, rational runtime and250tests9.851s;
inventory passed250tests10.780s. Full build/lint/axioms remain unaccepted.
See M06-rooted-stored-query-1bc8827-failure.md for complete diagnostic,
artifact metadata, all-consumer type review and its static-only limits.

The new PBSRootStoredValue/PBSRootStoredState batch connects the actual rooted
parent's saved public-only MODEL law to the decoded original solver input.
Stopped histories remain in the saved posterior. Its discrepancy from the
internal live child is bounded by2*bound*stoppedPublicMass/publicReach for
each fixed continuation kernel. Independently recomputed scalar values add
both solver tolerances; actual fresh private security adds another fresh
tolerance. Both recursive Nash premises are derived from actual solvers.
Native state/private memory and actual selected-round prefix are unchanged.
A concrete noisy rooted hidden-type parent consumes the saved-law, scalar
and private-security results with its mass-scaled internal request, plus the
missing-PBS boundary. Five independent Fraction controls cover the failures.
See M06-rooted-stored-query-batch.md for scope, assumptions and static review.

Expected validation:202 build targets,164 targeted/304 global audit modules,
250 Python tests. All previous targets remain registered. New source is
unverified until same-SHA Actions and complete-log review. Solver definitions,
workflow/audit criteria, heartbeat limits and source pins are unchanged.
Commit-before type review is static, never a successful Lean check.

Next dependencies: native successive-query calibration and conditional
incumbent/selfplay/root/support costs; changing-clock connection; useful
solver-specific small bounds and full recursive safety; remaining original
SEARCH-CFRD/SEARCH-ERROR/SAFE-THEOREM3 acceptance. Decoded saved MODEL law is not
unknown factual law. Native private/history correlations and retained late draw
remain required; no prior reset or Nash-to-policy-closeness step is valid.
Prediction error, finite-T and childloss remain independent.

P-CFRD-AVERAGE/P-CFRD-TARGET and SEARCH-FRONTIER/P-SEARCH-SETUP/P-SEARCH-LEAF
remain accepted in existing journals. Frozen coverage.json stays at blob
2fc8cc9ad6607d61bfe397707fb96ac322fbb800. The previous dedicated ledger is
preserved byte-for-byte as M06-kernel-value-transport-coverage-at-1bc8827.json.
M06 and the full Theorem3 remain incomplete.
