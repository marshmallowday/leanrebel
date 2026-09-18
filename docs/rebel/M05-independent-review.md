# M05 independent source/domain review

## Preserved source and concurrent work

This review starts from main `8c7e273aae25e3bec21028c9bda6c8c3fcf680c1`
and preserves the independently added M05 checkpoint
`0e70739cb3a703e526ff2c99b6a9511b6243f37d`.
Development is isolated on `rebel/m05-review` while `rebel/m05` may advance.
Do not overwrite concurrent changes or force-update either branch.

All 50 files recursively under `docs/rebel` at the main source were read,
including the complete decoded official inventory, all paper rows, source
metadata, reuse records, coverage overrides, historical logs and recovery
notes. The newly added M05 checkpoint was read separately. The source was
obtained through the GitHub plugin from artifact `10565422034`, run
`35390613688`. The source tar SHA-256 is
`6c0c81357d0a335722777e90aca0104a0adc5d44a2083ac80db89471919e01e9`.
Offline inspection of the plugin-provided snapshot does not make a local
GitHub connection.

On that unchanged source, the coverage and inventory validators pass and all
54 Python regression tests pass. These are metadata checks, not evidence of
new Lean proofs. No M05 coverage row is promoted by this checkpoint.

## Source distinctions to retain

The published main paper p5 states an existence claim about an extension in
Theorem 1. Supplement F pp19-20 instead uses a particular degree-zero radial
normalization and asserts its concavity. These are different obligations.
The supplement's normalization is not generally concave; M01's rational
example is useful but still needs an actual game/value connection.

The intended proof route separates:

- canonical finite PBS-game equilibrium existence and value uniqueness;
- legal typewise best-response pasting with fixed compatible conditional
  history laws, including own-zero-probability types;
- minimax and concavity on the own-belief simplex;
- centered supporting vectors, a distinct concave extension agreeing on the
  simplex, and the failure of global support for the radial extension;
- boundary, nonunique-equilibrium and nonsmooth controls.

A convex combination of supporting vectors requires nonnegative weights
summing to one. Footnote 8's arbitrary linear-combination wording is not
justified by convexity alone. Preserve this distinction in the source ledger.

Do not assume Lemma 1's conclusion as a field, replace correlated beliefs by
products of marginals, infer equilibrium existence from value uniqueness,
or silently treat the repaired extension as the supplement's extension.
M05 remains pending until the proof, integration and exact-source CI gates
are complete. Dependencies and audit budgets remain unchanged.
