# ReBeL status — M06 in progress; M05 accepted

## Current resume point

Resume from the remote HEAD of rebel/m06-uniform-source-rates-20260924.
This extension follows repair8a82e7fdee7cd7fc23c1b40609ab7c869750939e on
rebel/m06-source-rates-repair-20260924. The repair branch and failed predecessor
bd5cdaa304cb0791379c94fd0454ed28eabb683d on rebel/m06-transport-rates-20260924
are preserved; main is not a write target.

The source-rate repair passed M06 target36003811993/job107646728317:131 targets,
1474 transitively audited declarations, and normal/slow lint over93 modules.
Inventory36003811987 and source snapshot107646727703 passed. FullCI36003811808/
job107646730056 is SUCCESS, including all architecture and whole-library gates.
Independent ReBeL36003811764/job107646727800 is still being checked; do not infer
its final success from the target. The original source failure and exact repair
are in M06-source-rates-compiler-loop.md.

The new extension adds a structural game-dependent density cap, an explicit
opponent-uniform source-law rate and an actual two-fresh-solve consumer. Initial
source2264eefd5c25f99b606e9c83ca94e5f536a3d8d9 failed M06target36005895147/
job107653834466 on unused section typeclass assumptions in DominatingReachBound.
The current checkpoint removes the unused Fintype-player premise and scopes
DecidableEq only to the theorem requiring it; no linter is disabled and proof
bodies/conclusions are unchanged. See M06-uniform-source-rates.md for exact
failure evidence, source locators, assumptions and scope. All three new modules
remain in the analytic root, target and axiom/lint consumers:134 targets and96
supplemental modules preserve every prior entry.

This extension remains UNVERIFIED until the repaired source's compiler,
normal/slow lint, transitive axiom and whole-library gates are inspected.
Do not accept from source existence or Python tests. No inherited theorem,
target, workflow, dependency pin, warning policy or whitelist is weakened.
coverage.json parent statuses stay pending.

## Predecessor independent gate resolved

The predecessor independent ReBeL run35984130849/job107582791762 was rechecked
through the GitHub plugin during this continuation and is now SUCCESS. All
compiler/lint/transitive-axiom, rational solver and tracked-cleanliness steps
succeeded. This resolves the last outstanding independent gate recorded in the
weighted-transport review. Its exact-source snapshot job107582792124 also passed.
The accepted source remains fd3770c4c4123cefec9cc5456f99b18f5b52c697 on
rebel/m06-weighted-transport-20260924, with documentation review HEAD
1c509f60f823505a36318e54735f61e00dd49aab on
rebel/m06-weighted-transport-reviewed-20260924. Neither ref is moved here.

## Accepted weighted-transport evidence

M06target35984130871/job107582693551: SUCCESS at2026-09-24T10:07:53Z.
All128 declared targets compiled, then supplemental lint and public/private/
generated transitive axiom audit passed with
EXACT_LEAF_AXIOM_AUDIT_PASS declarations=1396 and
EXACT_LEAF_VALIDATION_PASS modules=90 under Lean4.33.1.
FullCI35984130854/job107582847450: SUCCESS at2026-09-24T10:12:20Z,
including whole-library build, inventory/reuse signatures, architecture Phases1/2/3,
reachability probes, library lint and tracked-file cleanliness.
Inventory35984130885/job107582693947 also passed. Preserve exact artifacts,
initial failure and repairs in M06-weighted-transport-validation.md and
M06-weighted-transport-compiler-loop.md. Only propext, Classical.choice and
Quot.sound are allowed. No inherited gate, workflow, pin or whitelist is weakened.

CFRDWeightedTransport integrates live child loss, positive model-value change
and conditional transport under the ACTUAL privateCarriedPrefix joint law.
Perfect recall supplies the unknown-opponent change of measure; no model PBS is
identified with an actual posterior and no independent seed/history resampling
is substituted. Its source does not prove a vanishing rate by expectation alone.
The fresh-chain consumer constructs a noisy parent and actual finite children,
retaining finite T and positive noise. The canonical control has bias1/8 and
fresh tolerances1/4 then1/8. Preserve its theorem scope and numerical/proof split.

## Older accepted checkpoints and remaining work

Recovered reference-transport source d7ab37e1e36b0c89dde76dd03bce5505e99163b0
has all target, full CI, independent ReBeL and inventory/snapshot gates SUCCESS.
The prior fresh-chain source46126f37 independent run35964794487 also succeeded.
Preserve44a98bb4,66a8b9ec,composition639e3962,recursiona4246792/reviewa5e0700f,
budget704e96ff,nestedf9d4def1,repair751ad17a and all accepted M05 records.

Remaining: shrinking source outcome/reference radii for the intended algorithm,
useful native first-exit rates, independent re-solving at later carried PBSs and
CarriedResolveStepBounds. The new work must connect actual source-law discrepancies,
not assume a desired root safety inequality. Coherent final-average sampling is
still different from the native-iteration sampler. SEARCH-FRONTIER, SEARCH-CFRD,
SEARCH-ERROR and SAFE-THEOREM3 remain pending; coverage statuses are not promoted.
Preserve the printed/corrected Theorem3 distinction and the proof/executable-
numerical boundary. Do not reapply stale reweight ZIPs or redo accepted slices.
