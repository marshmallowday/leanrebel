# Recomputed-value documentation lint failure on d9c73f0

Exact source: d9c73f034e9a1600acbaa5b77c22ffdd0e76674a.
Parent batch: cbda1b336c5a8705813376340597cfba51851021.
Last fully accepted dependency remains ce81eaecde20fb02de0a191ba1ceb64e32bafe16.
This is a failed-candidate review, not acceptance of M06 or its source obligations.

## Complete Actions evidence

All four runs were completed and their head_sha matched the exact source.
The complete decoded logs of all four jobs were obtained through the GitHub
plugin and scanned, including multiline transitive axiom records.
Artifact metadata was read; binary ZIP contents were not read.

| Workflow | Run / job | Result |
| --- | --- | --- |
| CI | [36416665284](https://github.com/marshmallowday/leanrebel/actions/runs/36416665284) / 108909319237 | failure at full-library lint |
| ReBeL checks | [36416665256](https://github.com/marshmallowday/leanrebel/actions/runs/36416665256) / 108909319048 | failure at documentation lint |
| M06 targeted | [36416665342](https://github.com/marshmallowday/leanrebel/actions/runs/36416665342) / 108909318819 | failure at documentation lint |
| Source inventory | [36416665258](https://github.com/marshmallowday/leanrebel/actions/runs/36416665258) / 108909318613 | success |

The previous conditional-instance rewrite errors are resolved: core, concrete
examples and umbrella compile. CI reports full build success (4307 jobs) and
lint-module build success (4077 jobs), all three architecture VERIFIED=1
results, TRANSPORT_ANALYSIS_SOURCE=0 and LIBRARY_LINES_OVER_100=0.
ReBeL checks also reports these two static metrics at zero, RATIONAL_RUNTIME_PASS,
and 210 Python tests in 8.218s. Inventory reports 210 tests in 10.105s.

All 2275 targeted and 5411 global unique transitive axiom records were parsed,
including wrapped lists. Only propext, Classical.choice and Quot.sound occur.
This is exact-source evidence for those gates, not evidence of complete lint:
targeted has one LINT_PASS before stopping; global has 43 before stopping at
the umbrella. Neither complete normal/slow lint suite has passed.

## Shared diagnostics and repair

All three failed jobs report precisely these four source lint diagnostics
at PBSRecursiveRecomputedValue.lean:27-30:

- PBSRecursiveResolveConfig.noise definition missing documentation string.
- PBSRecursiveResolveConfig.cuts definition missing documentation string.
- PBSRecursiveResolveConfig.tolerance definition missing documentation string.
- PBSRecursiveResolveConfig.fuel definition missing documentation string.

The structure itself was documented, but its four generated projections were
not. Add one docstring to each existing field, describing actual noise
allocation, recursive cut schedule, requested tolerance and stage fuel
excluding the late horizon. No field type, order, definition, theorem statement,
proof, instance, assumption or deployed algorithm changes. No linter suppression,
workflow edit, target removal, heartbeat increase or test weakening.

## Precommit review and limits

The actual field signatures remain PBSRecursiveDepthNoise.{u}, List Nat, real
tolerance and Nat fuel in that order. pbsRecursiveConfigStage still passes the
same noise/cuts/tolerance/fuel to pbsRecursiveDepthStage. The recomputed outcome,
loss, native sequence budget, initial-security consumer and all three concrete
examples retain their existing types and terms. In particular, positional
constructors keep their four arguments, state-indexed PublicBelief and full
information signal carriers are unchanged, and the two-stage example retains
totalFuel=3 (two stage steps plus one late step).
The posterior module, its implicit full-model conditioning parameter and
typed PBSChildSolve consumer were reread; all are unchanged.

A direct text comparison after removing doc comments and whitespace confirms
the executable Lean text is identical to d9c73f0. All core lines remain at most
100 characters. This static check is not Lean compilation. Compiler and all
lint/axiom gates must be checked again on the new SHA. No local Lean or Python
execution is claimed. The current repair loop remains open until that succeeds.

Artifacts: CI10968785171, global10968790060, targeted10967822002,
source10967796004. Inventory has no artifact.
Their metadata and exact-SHA links were inspected; decoded job logs, not ZIP
contents, are the validation evidence.

The 178 build targets, 140 targeted / 281 global modules and 210 Python tests
remain required. Frozen coverage.json and accepted source journals are unchanged.
Computed native budgets are not yet shown small; rooted-child/fresh-solver
correspondence and SEARCH-CFRD/SEARCH-ERROR/SAFE-THEOREM3 remain pending.
