# M06 query-sampling restart — 2026-09-21

## Restart source and exact observed failure

Resume from integration commit `8ec014ee7b5a2fe8d709e50512d3c58364dc0b6e`
(tree `619e4cce946a682f4078a173558c123a00bd85f6`), not the older
`c60f3b20d333557adb39509399b92029e64f005e` checkpoint. Both existing
`rebel/m06-sampling-validation-20260921` and
`rebel/m06-independent-sampling-checkpoint-20260921` pointed to the integration
commit when inspected. Main remains the accepted M05 source
`6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`.

The integration's CI run `35571011975`, job `106242460247`, was inspected.
On the pinned Lean 4.33.1 it completed `lake build` (4222 jobs), compiler-resolved
inventory checks and all three architecture gates. Its full-library lint
failed with exactly one `defsWithUnderscore` finding:
`GameTheory.ReBeL.pbsInformationCFR_sampleFrom` at
`GameTheory/Analysis/ReBeL/PBSSupportedSampling.lean:117`.
The tracked-file cleanliness step was skipped after the failure; do not claim
that step passed. Source inventory run `35571012090` succeeded.

## Focused repair

Rename the definition and all its source/example uses to
`pbsInformationCFRSampleFrom`. No proof statement, assumption, linter, axiom
allowlist, dependency or adversarial example is weakened. The new source needs
its own compiler, lint and axiom evidence; the parent build is not that evidence.
Implementation continues on `rebel/m06-query-sampling-20260921`.

## Next dependency-closed slice

Connect actual retained child-iteration laws to the parent's canonical
counterfactual/type-conditioned queries, including the existing zero-own-reach
completion branch. Supported-root reweighting and independent one-PBS sampling
already exist and must not be reimplemented as new progress. After this query
bridge, the remaining target is recursively re-solved carried-PBS play against
a fixed unknown opponent, with explicit finite-iteration and prediction losses.

Original `SEARCH-FRONTIER`, `SEARCH-CFRD`, `SEARCH-ERROR` and `SAFE-THEOREM3`
coverage obligations remain pending. Neither a lint repair nor a conditional
one-cut law is full M06 acceptance. Keep the printed Theorem 3 and its corrected
finite-T interpretation distinct. Preserve all predecessor evidence in
`M06-sampling-validation-restart.md` and the Git history.
