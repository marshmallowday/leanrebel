# ReBeL status — M06 in progress; M05 accepted

## Current resume point

Resume from the remote HEAD of rebel/m06-transport-rates-20260924.
The source-atom transport draft was checkpointed at
cc4bf7aecb83f75929f568bf0dd4950578d4cafa after restart checkpoint53e99a3b.
Its FinDistTransportRate module is now appended to the analytic root, M06 target
list and supplemental transitive audit. All128 inherited targets and90 inherited
audit modules are preserved. Current counts are129 targets and91 audit modules.
At this checkpoint the new proof has NOT yet passed exact-source compiler/lint/
axiom validation. Inspect CI for the remote HEAD; do not accept merely from source
existence. Continue with game consumers and adversarial controls described in
M06-transport-rates.md. Main is not a write target.

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

Remaining: source-level weighted drift/transport and native first-exit rates,
independent re-solving at later carried PBSs and CarriedResolveStepBounds.
The new work must connect actual source-law discrepancies, not assume a desired
root safety inequality. Coherent final-average sampling is still different from
the native-iteration sampler. SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and
SAFE-THEOREM3 remain pending; coverage.json statuses are not promoted.
Preserve the printed/corrected Theorem3 distinction and the proof/executable-
numerical boundary. Do not reapply stale reweight ZIPs or redo accepted slices.
