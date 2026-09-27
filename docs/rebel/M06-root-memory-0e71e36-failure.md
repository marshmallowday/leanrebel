# M06 retained-root repair: 0e71e36 compiler feedback

Source 0e71e36f7d5521b2875c21713ad7024602e6f6a3 is not accepted.
Continue rebel/m06-kernel-value-repair-20260927 from that re-read HEAD.
Main remains 6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098. The plugin
reconfirmed marshmallowday/admin. The next repair changes proof bodies only.

## Exact-SHA evidence

Complete decoded logs were read for:
- [CI 36348410281](https://github.com/marshmallowday/leanrebel/actions/runs/36348410281),
  job 108702169287: full build failed.
- [ReBeL checks 36348410156](https://github.com/marshmallowday/leanrebel/actions/runs/36348410156),
  job 108702168738: proof-module build failed;
  source snapshot job 108702168876 succeeded.
- [M06 targeted 36348410270](https://github.com/marshmallowday/leanrebel/actions/runs/36348410270),
  job 108702169074: target build failed.
- [Inventory 36348410269](https://github.com/marshmallowday/leanrebel/actions/runs/36348410269),
  job 108702169319: success, 181 tests in 9.738s.

Every run head_sha matched the failed source. The three compiler jobs
reported the same five diagnostics, arising from three remaining causes.
FinDistRetainedLabel compiled. Checks passed LIBRARY_LINES_OVER_100=0,
TRANSPORT_ANALYSIS_SOURCE=0, all 181 Python tests in 8.828s and
RATIONAL_RUNTIME_PASS. Complete normal/slow lint and transitive-axiom audit
were not reached, so no full acceptance is inferred.

Artifact metadata: target 10941418755
(sha256:f6ffa0ea07e6caac385143e1aa3eaf8053b773509574183a2ac348b61e01dc1b),
global 10942160870
(sha256:b09ab6be189d7ae1d9e113a67a2b107fcad1bd54a95ed07a0ec6906f2455f2e6),
snapshot 10941089479
(sha256:942cf4fe25e1e82b73900a896f84772b81a5bdeae294fadd7a0d269291d51de1).
CI/inventory had no artifacts. Binary archives were not downloaded; actual
complete decoded job output supplies the compiler evidence.

## Combined repair

All locations refer to CFRDValueTargetMemory.lean in 0e71e36.
- Line 189: both Function.comp_apply and Option.map_some are unused simp
  arguments. Remove the redundant simplification step; keep the Option.map
  representation and retained-label theorem.
- Line 240: fiber recoding succeeds, leaving the same conditional law on
  both sides but callbacks (some h).elim 0 payoff and payoff. Close the
  observed definitional equality explicitly with rfl.
- Line 324: cases h.state rewrites the explicit Option.elim expression but
  cannot expose the state inside the still-folded pbsRootPayoff callback.
  Unfold pbsRootPayoff before the case split, then each branch closes by rfl.

The earlier concrete snapshot, rooted readout reduction, Option.map
recoding, explicitly instantiated pushforward equality and complete trace
function equality no longer produce their former diagnostics. This does not
assert that downstream example compilation or full lint has passed.

The mathematical statements, definitions, premises, tests, workflows and
audit rules are unchanged. Source-level header comparison confirms the same
declaration statements. Keep 160 build targets, 122 targeted/264 global
modules, 181 Python tests and frozen coverage blob
2fc8cc9ad6607d61bfe397707fb96ac322fbb800. No Lean/Python was executed inside
the plugin. The previous accepted d2af110 result is not reused for this source.

The repaired source remains pending exact-SHA Actions. M06 root-target source
acceptance, small-cost recursive solver analysis, full recursive posterior
comparison and SEARCH-CFRD/SEARCH-ERROR/SAFE-THEOREM3 remain unfinished.
