# ReBeL status — native randomized resolver support, M06 incomplete

## Resume point

Continue the latest HEAD of `rebel/m06-resolver-support-20260927`. It descends
from latest starting checkpoint 3d272004909c9e70226aeb430813d3d53f038fdd,
support implementation b833d49b430ac44c433658f3cc72fd130ff0a87f, and integrated
7326f1e40011b1d4329f09e743491cc7bc7e5746. Main remains accepted M05 at
6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098. No force-push or branch deletion.

9894e45bbc0505debd44957a4a7446302d2b7902 added seven native resolver-support
definitions/theorems, retaining the chosen profile/model/history coupling and
averaging the result over actual full-state laws. 63aa262540b7dc633ea511c6cc727aaa49bde585
added four Lean controls and eight exact Fraction tests. e0e46a994be4c0e5c0d5096cf4c59f11bad84f38
removed two authored transport steps to satisfy the unchanged zero budget.
461a926c198d0801ab659b4d1773ded7fd6fd5f8 repaired the negative control's bind
identity and an unused simp argument. The current successor repairs only the
stopped-state indicator proof, without changing any statement or assumption.

Read M06-resolver-support.md for semantics, M06-resolver-support-controls.md
for consumers, and the subordinate coverage JSON for declaration identities.
The validation history and separate 63aa/461 failure records retain actual
failed attempts instead of silently presenting them as passed.

## Validation state

The complete new slice is NOT yet compiler/lint/axiom accepted. 63aa's core
module compiled, but its example module failed and its separate global job
correctly rejected TRANSPORT_ANALYSIS_SOURCE=2. The transport repair kept the
budget at zero. 461's static architecture and line-width steps passed, but
its target run 36281256829 / job 108513412501 failed at the stopped branch's
existential simplification. Its complete artifact 10918699965 was inspected;
see M06-resolver-support-461-failure.md. The current repair proves the indicator
comparison separately and uses native definitional equality, not a transport
step. Inspect its own target SHA and all subsequent validation before acceptance.

Both downloaded exact 63aa and 461 source snapshots passed all 120 Python
fixtures locally, including the new 4,374 exact kernel-grid cases. These are
not Lean proofs. Both source inventories passed. Original examples, coverage,
proof statements, audit/target consumers, architecture/workflow gates, umbrella
and dependency pins remain unchanged. No local Git or direct GitHub HTTP was used.

The inherited b833 GLOBAL run 36277876590 / job 108504099546 succeeded and its
complete artifact 10918521959 was actually inspected: 4,939 fully parsed
allowlisted transitive axiom records, 253 module lint passes, global validation
and frozen architecture pass. M06-support-rates-b833-global-validation.md
records the exact hashes and scope. That closes baseline validation only;
it does not certify later declarations. Earlier failed and target/full-CI
records remain intact.

## Next action and unclosed obligations

Fetch the latest repaired HEAD's targeted compiler output, normal/slow lint and
all transitive axiom records. Check full/global jobs separately, retaining exact
SHA/run/job identities and pending versus failed versus successful outcomes.
Do not repeat the completed baseline work or infer acceptance from names.

Native finite-schedule first-exit composition, small primitive support leakage,
changed-PBS native/late value gaps and source-specific CarriedResolveStepBounds
remain open. Support containment alone is neither actual/model posterior equality
nor a security value bound. Keep joint-type compatibility, actual public event
denominators, the same unknown comparison opponent and finite-T residuals.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
M06 is incomplete; no learner convergence premise bypasses test-time safety.
