# Stored-child acceptance at 133dc24

Commit: 133dc247945486c48f055815b4262261f6fff5f2.
Branch: rebel/m06-kernel-value-repair-20260927.
All four runs report this exact head SHA and completed/success.

| Workflow | Run | Job |
| --- | --- | --- |
| CI | [36390994514](https://github.com/marshmallowday/leanrebel/actions/runs/36390994514) | 108826546365 |
| ReBeL checks | [36390994487](https://github.com/marshmallowday/leanrebel/actions/runs/36390994487) | 108826545910 |
| M06 targeted | [36390994535](https://github.com/marshmallowday/leanrebel/actions/runs/36390994535) | 108826546503 |
| Source inventory | [36390994579](https://github.com/marshmallowday/leanrebel/actions/runs/36390994579) | 108826546488 |

Complete decoded job logs were read through the GitHub plugin. All 2192 targeted
and 5333 global unique transitive axiom records were parsed, including multiline
lists; record-start, parsed-record and unique-name counts match exactly.
Every list contains only propext, Classical.choice and Quot.sound, or is empty.
All 134 targeted and 276 global module lint passes and validation end markers
were present. The audit scripts run the existing full Batteries linter trace;
neither normal nor slow checks were suppressed.

CI full build completed 4301 jobs and lint build 4071, with all three architecture
VERIFIED=1 checks. ReBeL checks report LIBRARY_LINES_OVER_100=0,
TRANSPORT_ANALYSIS_SOURCE=0, RATIONAL_RUNTIME_PASS and 200 Python tests in
7.747 seconds, OK. Inventory reports 200 tests in 8.217 seconds, OK.
The manifest has 172 build targets.

Artifact metadata was inspected: CI10955914150, global10957721620,
target10956073922, source10956516952 (snapshot job108826546250).
Inventory has no artifacts. Binary archives were not downloaded; complete
axiom and compiler evidence came from the decoded logs.

Accepted dependency source blobs:
- CFRDStoredChild.lean: ca04ee7940fb9d65b902e6657629a8ed05df0ad2
- PBSStoredChildReplay.lean: 0ff1876a2c809055a953cc9a0948cc585a97e5dc
- Examples/PBSStoredChildReplay.lean: 19b18193300a7d6c0007d904f366db1a0216b7e2
- test_stored_child.py: d44cab1ad03d2eceab1ef57e2295380f4cebb5ac

M06-stored-child-batch.md remains the scope: actual same-round noisy parent,
initial stored MODEL law, publicly visible termination, factual child input and
exact mass-scaled budget; supported replay under a fixed unknown opponent through
arbitrary late fuel. All previous elaboration/index errors are resolved.
This is not an equivalence between differently configured rooted and original
solvers, or a proof of actual hidden support or small fresh replacement loss.
SEARCH-CFRD, SEARCH-ERROR, SAFE-THEOREM3 and M06 remain incomplete.
New discarded-mass source requires new-SHA Actions and semantic acceptance.
