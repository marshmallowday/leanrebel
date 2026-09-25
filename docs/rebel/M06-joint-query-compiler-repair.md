# M06 joint-query compiler feedback and second repair

Initial source: `ada439cebe48ad3c522afd95c61c2efe32412bde`.
Architecture/test repair parent: `8179309e5adb72d9fd848b7712d8aac870f73646`.
Continue on `rebel/m06-joint-query-repair-20260925` from its current head,
not from the failed initial implementation. All historical checkpoints remain.

## Actual initial compiler feedback

Target run `36148111692`, job `108114248701`, completed FAILURE. Its actual
artifact `10870499480` was downloaded through the GitHub plugin:
ZIP SHA-256 `5f6ce554efa50d82037b6ba0b7e5ebd6214c0b295f3a75f080146837a24a2e4c`;
log SHA-256 `7dced16c196a6e8383ae0d5ed29e0f64d71eae26a747fc16ec9e7197cdae290f`.
The log identifies ada439c and the pinned Lean v4.33.1 toolchain.
It explicitly BUILT GameTheory.Analysis.ReBeL.PBSJointNativeGap, so the three
new main theorems compiled even before the density-hypothesis rename.
This compiler success is not transitive axiom or configured lint evidence.
The targeted lint/axiom step was SKIPPED after the example compilation failed.

The control module reported an unknown FinDist.map_map at line 87, and open
marginal-map and product-expectation goals at lines 86 and 95. The canonical
API is FinDist.map_comp, not map_map. This second repair uses map_comp and
map_id directly for the two marginals. The product mean proof explicitly
rewrites expect_product before finite summation; the original norm_num simp
set had instead expanded expectation over the whole product carrier first.
Every control statement and the sharp factor-two/unsupported-type distinction
is preserved. No source proof is admitted or weakened.

## Independent architecture repair evidence

For parent 8179309e5adb72d9fd848b7712d8aac870f73646, ReBeL run `36148730537`,
job `108116314777`, was re-read with both the line-width and static Phase 2
architecture steps SUCCESS. This confirms the identifier rename fixes the
observed lexical gate failure without changing the gate. Its compiler work
was still pending at that observation. Parent target `36148749730` /
`108116381897` and full CI `36148730659` / `108116316098` belong only to 8179309.
A later push may cancel those superseded runs; never attribute them to the
current repaired examples or infer completion from them.

The exact 8179309 source artifact `10870364272` has ZIP SHA-256
`878e40b6dbfd1b0394c889c04eac71a864fd5cb65fffefda09bbaf013a8ba23e` and tar
SHA-256 `3d70b3938c535adceb62fb01f03a402d1712e325a1b4294791712682fa1f593b`.
Its embedded commit was checked and all 87 Python tests were executed on
that exact extracted source with warnings treated as errors: SUCCESS.
Local test-log SHA-256:
`40a032b8e7d757bad3498346d3590f4cf42243c74f2fcd2b016295a765bbeddb`.
Coverage/inventory structure passed for all 3054 inherited items, with no
acceptance transition. Static discovery has 249 global modules, 104 targeted
auditor modules, 580 public Lean files and zero line-width violations.
No local Git or direct GitHub network call was used; no local Lean run is claimed.

## Current validation gate

The main proof keeps the architecture-safe jointDensity name. Only the two
example proof scripts are changed in this second repair. Run the exact current
head through the unchanged M06 compiler target workflow, strengthened 104-module
targeted lint/axiom auditor, independent all-ReBeL audit and full CI. Their
new-source results are PENDING at this commit. Read actual target-SHA logs
before acceptance, retaining run IDs and complete axiom sets.

M06 and Theorem 3 are NOT complete. The joint density cap is still an explicit
source-law condition; actual carried law construction and quantitative rates,
changing opponents/PBS and independent recursive re-solving remain unproved.
