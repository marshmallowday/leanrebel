# Carried-value dependency accepted at d771e88

## Exact source and scope

Accepted dependency commit: `d771e88c97ac1b244812a6d5da99900a61be64ba`.
Branch: rebel/m06-kernel-value-repair-20260927.
The original chat baseline is 9457c198126f3c8b7cb1045bbed2e0053788636f.
The batch began at ed2fad241260b8df23d7e47448a817ca9458e464; subsequent
repairs fixed an unused simp argument, a source-transport audit violation,
the concrete schedule-fuel rewrite, and one duplicate declaration name.
This acceptance does not cover later edits and does not complete M06.

The accepted meaning is described in M06-carried-value-batch.md. The stored
posterior is the chosen MODEL posterior, not the unknown opponent's factual
posterior. Execution discrepancy compares old and fresh own policies against
the same unknown opponent over stage fuel PLUS the late horizon. Its internal
prefix law is the old comparator; the inter-stage distribution is actual native
full-state execution. The derived charges are not claimed to be small merely
because a solver's Nash gap is small.

## Actual same-SHA validation

| Workflow | Run | Job | Result |
|---|---:|---:|---|
| CI | [36315829902](https://github.com/marshmallowday/leanrebel/actions/runs/36315829902) | 108610232019 | success |
| ReBeL checks | [36315829918](https://github.com/marshmallowday/leanrebel/actions/runs/36315829918) | 108610231974 | success |
| M06 targeted | [36315829868](https://github.com/marshmallowday/leanrebel/actions/runs/36315829868) | 108610231896 | success |
| source inventory | [36315829852](https://github.com/marshmallowday/leanrebel/actions/runs/36315829852) | 108610231945 | success |

The exact head_sha and completed/success state of each run were checked.
Complete decoded logs of all four jobs were inspected, including all 1949
targeted and 5099 global transitive axiom records. Every record uses only
propext, Classical.choice and Quot.sound, or no axioms. The counts match
EXACT_LEAF_AXIOM_AUDIT_PASS and REBEL_AXIOM_AUDIT_PASS.

All 118 targeted and 261 global module lint-pass records and final validation
markers are present. These are the unchanged normal/slow Batteries linter
invocations configured by the audit scripts, with trace output. CI also passed
the full library build, lake lint, all three architecture phases, inventory,
compiler-resolved reuse checks and tracked-file cleanliness. The Linux-specific
Windows toolchain exposure step was appropriately skipped.

ReBeL checks passed 160 Python tests in 8.034 seconds, and source inventory
passed 160 tests in 10.200 seconds. The rational Lean solver and independent
pure-response runtime comparison passed. Static diagnostics report
LIBRARY_LINES_OVER_100=0 and TRANSPORT_ANALYSIS_SOURCE=0.
The source snapshot job 108610232175 succeeded.
The 156 build targets and all existing audit modules are retained.

## Artifact metadata and defining source blobs

- ci-audits-d771e88c97ac1b244812a6d5da99900a61be64ba: artifact 10930822791; sha256:bbd0cd9830c96ed4eb73d27803500f86c0b5bae4c352e71b3ca62de02c2dd1a8
- m06-targeted-d771e88c97ac1b244812a6d5da99900a61be64ba: artifact 10930523085; sha256:1ff0ae403b439ae93f058a5bc24124511fbe99280af9e73283227956d64d2240
- rebel-validation-d771e88c97ac1b244812a6d5da99900a61be64ba: artifact 10930829430; sha256:de7d6ba644092d63b2c99707540372afdfa8761ac4aded1109f69d8ee5e349b2
- rebel-source-d771e88c97ac1b244812a6d5da99900a61be64ba: artifact 10930313942; sha256:41c8bbceed6931fccb8dcb3f620db7a7045c67405aaaba69a8011b74e90f8bba

Binary archives were not downloaded. Claims above rely on the complete
decoded job logs and artifact metadata, not an uninspected archive.

- GameTheory/Analysis/ReBeL/PBSOpponentModelTransport.lean: 2267714436bb251e0fce2169936f20472262f988
- GameTheory/Analysis/ReBeL/PBSKernelValueTransport.lean: 6c69f28c67858621d887724d0bb9dd9355940680
- GameTheory/Analysis/ReBeL/PBSCarriedValue.lean: 483061ef625a5cb381ab60a44ebf51546c2cff35
- GameTheory/Analysis/ReBeL/Examples/PBSCarriedValue.lean: 79bfb5020a8f1627c9017e18d9901330d262c98b
- scripts/rebel/tests/test_carried_value_transport.py: f4c047adf113b594c09e82a29fe1f7cc488ec4f9

## Still open

Specific recursive type-kernel/value comparisons, small solver-specific rates
or tighter signed envelopes, and original SEARCH-FRONTIER, SEARCH-CFRD,
SEARCH-ERROR and SAFE-THEOREM3 acceptance remain open. This is dependency
acceptance only; the original coverage obligations are not promoted.
