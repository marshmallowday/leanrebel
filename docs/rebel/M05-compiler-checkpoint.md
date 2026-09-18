# M05 finite-value compiler checkpoint

M05 remains in progress. The main branch is unchanged at the validated M04
source. Development continues on `rebel/m05` through non-force GitHub-plugin
ref updates. No coverage item is promoted by this checkpoint.

## Exact result for 015faf4206d97cafdb19c5c647ea8d6cf157f183

Full CI `35393791141`, job `105757860202`, compiled `TypeValue.lean`
successfully. Its typewise finite maximum, simultaneous legal type-plan
response, finite minimax attainment, and optimal-opponent characterization
passed the Lean compiler. This is not yet the entire PBS value bridge.

That CI failed on one trace-length unfolding in `ContinuationConsistency`
and three local elaboration issues in `ValueGeometry`: pointwise versus Pi
scalar multiplication, missing parentheses around a summand, and the order of
an added real constant in an inequality. The next source fixes these without
weakening their statements or disabling lint. Dependent continuation
realization was not validated in that failed run.

## Added compiler candidates

- `ContinuationDeviations`: finite predrawing for all unilateral behavioral
  deviations from every legal root, integrated over the correlated joint PBS.
- `BeliefExistence`: actual finite-plan Nash existence transferred via complete
  outcome-law and unilateral-deviation equalities to behavioral and public
  prescription games. Existence is not supplied as a hypothesis.
- `RootTypeMemory`: full-AOH truncation and legal typewise policy splicing,
  with a structural information-memory condition rather than a payoff axiom.
- `Examples/ValueGeometry`: canonical finite zero-sum game controls for radial
  normalization failure, a repaired positive control, a zero-type boundary,
  and a genuinely nondifferentiable coin game with multiple optimal opponents.

All new files are compiler candidates until the exact pushed SHA passes.
The branch-only targeted workflow accelerates diagnostics; it neither replaces
nor relaxes full compilation, lint, architecture, inventory or transitive axiom
acceptance gates.

Remaining work includes the fixed compatible conditional-history slice,
canonical conditional best responses and their simultaneous attainment,
the PBS value/minimax bridge, applicable source calculus, complete semantic
review, justified coverage/status updates and all final acceptance checks.
