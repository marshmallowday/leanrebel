# ReBeL status — changed-kernel elaboration repair; M06 incomplete

Continue rebel/m06-kernel-value-repair-20260927, starting from latest prior
checkpoint dac8bd902ba368357d4a53f0d0b6b90a6d3dddeb. The second repair is a
child of 6b7865e312af3108568566187468e4df97bbd8eb, not main. All prior branches,
source failures and accepted 51d5 results remain preserved.

## Immediate task and checkpoint

The reserved recall binders in original 3ef5 were repaired at 6b7865. Its exact
TARGET run 36292478763 / job 108545087124 FAILED; the complete downloaded
artifact 10923021191 exposed three elaboration issues: lambda-applied attainment
rewriting, abs_add not found, and additive monotonicity on the wrong side.
The second repair beta-normalizes both actual attainment equalities, uses
abs_add_le, and supplies explicit add_le_add/le_rfl steps in core and integration.
No mathematical statement or acceptance gate is weakened or removed.

Next inspect this new source's targeted compilation, then complete normal/slow
lint and transitive axioms. Expected counts remain 116 targeted / 259 global
modules; the build manifest still has 154 entries. Global and full-CI are
separate gates. See M06-kernel-value-repair-6b7865-validation.md and the owner
M06-kernel-value-transport-coverage.json. Historical owner ledgers are archived
at both dac8 and 6b7865. No Lean acceptance of this slice is yet claimed.

## Exact-source evidence already inspected

6b7865 source artifact 10922154886 was downloaded through the GitHub plugin;
commit and archive hashes, all seven source/consumer pins, and the nine-token
first repair were checked locally without git operations or direct GitHub access.
Coverage and inventory structure checks plus all 149 Python tests passed on that
exact source. INVENTORY 36292478778 succeeded. These results do not validate
Lean or the new second-repair source. The old 6b7865 GLOBAL 36292478764 /
job 108545223929 and FULL CI 36292478756 / job 108545228737 had no final inspected
result at this checkpoint and may be superseded by the new-source push.

## Preserved mathematical scope and accepted inherited evidence

The generic slice compares complete compatible joint-history kernels with the
SAME opposing policies and horizon. Its depth integration retains the actual
correlated event-selected seed/type law, finite-T budget and positive event
probability. Fresh kernels may be seed-dependent and types explicitly retagged.
51d525ecbce26a1ba5ddaf9033aca7daa73dce23 target/global/full-CI acceptance remains
separate in M06-depth-native-gap-target-accepted.md and
M06-depth-native-gap-global-accepted.md; it cannot accept these new sources.

## Open mathematical obligations

Fresh compatible kernels remain explicit data, not actual recursively re-solved
posteriors. Full L1 discrepancy need not be small. Changed opposing policies,
source-specific small kernel/leakage rates, late-value transport and constructed
signed CarriedResolveStepBounds remain open. SEARCH-FRONTIER, SEARCH-CFRD,
SEARCH-ERROR and SAFE-THEOREM3 remain pending. M06 is incomplete; learner
convergence is not independent test-time safety.
