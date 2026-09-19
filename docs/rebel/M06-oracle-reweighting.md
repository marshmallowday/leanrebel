# M06 checkpoint: complete renewed review and oracle reweighting

## Renewed document review

All 68 files recursively under `docs/rebel` at
`9c1625ee92bc25ed33914b58a641403739825e67` were read in full, including every
checkpoint, the coverage journals, all TSV rows, and all keys and values of
the JSON inventories (decompressing the compressed official inventory).
The lossless review was divided into 59 contiguous chunks; truncated outputs
were reread separately. This is a review of the inventory contents, not a
claim to have read every original C++ or Python implementation body.

The deterministic file manifest consists of one UTF-8 line per sorted path:
`SHA256(file bytes)`, two spaces, repository-relative path, newline. Its SHA256
is `c67f66ca36c31b5886f707288fa5db9384e24f84d0b6bb6311797f244a8b80e2`.
GitHub's comparison confirms that the two inherited commits up to
`f179d3ff2956b5798825c642cb05c6d6de8ed8e0` changed only CFRDRegret and the
targeted workflow, not the reviewed documents. The recovery record added
subsequently and this new checkpoint are also reviewed.

## Compiled progress, not M06 acceptance

The repaired CFR-D root-regret proof at
`b133119a4f4956afdb5f9957ba89e72183521f84` passes the exact pinned Lean compiler
and targeted Actions run `35455661833`. Inventory run `35455661840` passes.
The full ReBeL run `35455661827` has passed line width, architecture, ledger,
fixtures and rational-runtime checks; its whole-module compiler/lint/axiom
step was still running when this checkpoint was prepared.

`OracleReweighting.lean` adds finite-law proofs that a single conditional
information-state value vector remains exact under an information-local
change of density. A uniformly delta-accurate vector remains delta-accurate
under the normalized changed law, with no unnecessary maximum-density
factor. Domination of support is proved. The module compiles locally under
the pinned Lean 4.33.1 and is included in the public root and targeted CI.

These lemmas do NOT yet assert that every strategic deviation has the
required density: that game-semantic bridge remains to be proved. Nor do
ordinary on-path values certify counterfactual best responses in unsearched
continuations. Continue with those bridges, the finite-time constants,
private random-iteration/carried-belief execution and adversarial controls.
No coverage row or milestone status is promoted by this checkpoint.
