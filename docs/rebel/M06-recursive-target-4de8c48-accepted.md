# Recursive training output accepted at 4de8c48

Branch: rebel/m06-kernel-value-repair-20260927.
Accepted SHA: 4de8c48f532575440c8159dfe15c96fc1c7180f0.
Original batch: 7711b65f98851187eef0e05c66b5ba569e03ccf0.
Chat baseline: 9457c198126f3c8b7cb1045bbed2e0053788636f.
Read-only GitHub plugin checks reconfirmed marshmallowday/admin, the work HEAD,
and default main 6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098.

## Exact-SHA verification

Every run reported this head_sha and success:

| Workflow | Run | Job |
| --- | --- | --- |
| CI | [36358641830](https://github.com/marshmallowday/leanrebel/actions/runs/36358641830) | 108731272133 |
| ReBeL checks | [36358641785](https://github.com/marshmallowday/leanrebel/actions/runs/36358641785) | 108731271893 |
| M06 targeted | [36358641774](https://github.com/marshmallowday/leanrebel/actions/runs/36358641774) | 108731272601 |
| Source inventory | [36358641777](https://github.com/marshmallowday/leanrebel/actions/runs/36358641777) | 108731271726 |

Complete decoded job logs were read through the GitHub plugin. All multiline
axiom records were parsed, including private declarations: 2097 unique targeted
and 5238 unique global records. Record-start counts matched parsed counts;
no axiom outside propext, Classical.choice and Quot.sound occurred.
All 125 targeted and 267 global module normal/slow lint passes were present.
The manifest contains 163 build targets. CI full build (4292 jobs), LintAll
build (4062 jobs) and lint, all three architecture verification phases, the
umbrella imports, rational runtime and tracked-tree cleanliness succeeded.

Checks reports LIBRARY_LINES_OVER_100=0, TRANSPORT_ANALYSIS_SOURCE=0,
RATIONAL_RUNTIME_PASS and 185 Python tests in 9.816 seconds.
Inventory reports 185 tests in 9.676 seconds. No local Lean or Python execution
was used. This acceptance does not verify any later source.

Artifact metadata was inspected, without downloading binary archives:

- CI 10944743854, sha256:9c132b31360f9b8681792a7fa67a2bcb6a5896079247663d5dcd32575d231f2b.
- Targeted 10945211039, sha256:c87fb7473496c349f5aabce1cc3b2e8e82f5b6bf011779f417672a6d9f46242e.
- Global 10944959271, sha256:9958b0107a93d7c0a48d5b84874315b3ee03330cb79ed44cd686909ab30d96c7.
- Snapshot 10945060279, sha256:f6f705f2b217c8cd14e1cccb2cbc456fd03104f5f8633579077cb46bc8770a4e.

The snapshot job 108731272115 succeeded. Inventory had no artifact.

## Accepted source and scope

- PBSComposedValueTarget: e997c5e10a60f57ae8f06a4681197520785aa8ce.
- PBSRecursiveValueTarget: 0dc5dd55906cdd919dd11a933ece010091bf27ff.
- Examples/PBSRecursiveValueTarget: 31f0855c69bbc734092b3429186886213cdd0e4c.
- test_recursive_value_target.py: a732facb10efaa054a37db73ba9ef754e3fa7f0b.

The proof-style repair closes the prior failure without changing definitions,
statements or assumptions. The composed and recursive targets use the actual
same-round child, noisy trace, finite count, original correlated joint PBS,
own AOH root conditioning and full remaining continuation. Administrative
root fuel is cut+1. Empty schedules and zero cuts are explicit.
The paired training output preserves the existing recursive policy and proves
its finite-budget Nash bound together with the numerical target-mean bound.

This accepts the dependency batch in M06-recursive-target-batch.md.
It does not establish target convergence to Nash information values, learned
network convergence, or small signed losses for independent fresh re-solving.
P-CFRD-AVERAGE and the remaining major source obligations are still pending.
