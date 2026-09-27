# M06 signed-kernel batch accepted at d54ec59

Exact accepted SHA: d54ec59cfaa17a117a9a720d1b85ba64842f4315.
Branch: rebel/m06-kernel-value-repair-20260927.
This accepts the dependency batch from 9d2bee9 and its subsequent repairs,
not the remaining original M06 source obligations.

## Same-SHA Actions evidence

All four runs were re-read with this exact head SHA and success conclusion.
Complete decoded job logs were read through the GitHub plugin.

| Workflow | Run | Job |
| --- | --- | --- |
| CI | [36325714671](https://github.com/marshmallowday/leanrebel/actions/runs/36325714671) | 108637977692 |
| ReBeL checks | [36325714645](https://github.com/marshmallowday/leanrebel/actions/runs/36325714645) | 108637977836 |
| M06 targeted | [36325714657](https://github.com/marshmallowday/leanrebel/actions/runs/36325714657) | 108637977713 |
| Source inventory | [36325714665](https://github.com/marshmallowday/leanrebel/actions/runs/36325714665) | 108637978961 |

Targeted log: all 1974 complete, unique EXACT_LEAF_AXIOMS records were parsed,
including multiline records, and checked against propext, Classical.choice,
Quot.sound. No other axiom occurred. All 118 module lint passes and the final
EXACT_LEAF_VALIDATION_PASS modules=118 marker are present.

Global log: all 5129 complete, unique REBEL_AXIOMS records were parsed and
checked against the same three permitted axioms; no other axiom occurred.
All 261 module lint passes and REBEL_VALIDATION_PASS modules=261 are present.
The existing auditors use collectAxioms and the unchanged Batteries
runLinter --no-build --trace loop (normal/slow validation surface).

CI passed full build, complete public-library lint, inventory and
compiler-resolved reuse signatures, Phase 1/2/3 architecture checks, and
tracked-file cleanliness. Checks passed LIBRARY_LINES_OVER_100=0,
TRANSPORT_ANALYSIS_SOURCE=0, rational Lean solver/runtime validation, and
164 Python tests in 9.056 seconds. Inventory independently passed 164 tests
in 9.725 seconds. The source snapshot job 108637977991 also succeeded.

Artifact metadata was read:
- CI 10934510842:
  sha256:a2cc6e876fab5daf6ea79ad115eab004e229c6655ef9e46e517541881542c460.
- Targeted 10934436055:
  sha256:603fe6762d509f9a017ee0525822888e7eb141c1fa9c9f47e12f18350f13c1fa.
- Global 10934453472:
  sha256:77170e7f7d036311da7dc7ef59351799029ba98cf8a0864a2d4b1af5a9eb9a1a.
- Source 10933644442:
  sha256:e5dfbded0c4be0d81074d78c6832533e1b71e23b9d3774de707b8e432364fe60.

Binary archives were not downloaded. Evidence is the complete decoded job
logs plus artifact metadata. No local build, lint, axiom audit or Python
execution is claimed.

## Semantic acceptance and limits

The statements and boundaries in M06-signed-kernel-batch.md were reviewed.
The seven omit annotations remove irrelevant implicit finiteness premises,
without altering proof bodies or mathematical conclusions. Supported type
kernels identify the stored selected MODEL posterior, not the unknown
opponent's factual posterior. Canonical stage-plus-late outcomes retain
the same private draw. Signed loss telescopes under actual forward full-state
laws. Couplings use NEW first, OLD second, so directed cost charges old-minus-new.

These are accepted dependencies. Small unrestricted-solver costs, complete
recursive comparison instantiation, and original SEARCH-FRONTIER/SEARCH-CFRD/
SEARCH-ERROR/SAFE-THEOREM3 acceptance remain pending. The finite-T term and
printed R5 discrepancy remain. This SHA's success does not validate later edits.
