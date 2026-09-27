# M06 carried-value joint-import feedback at c975ad7

The connected account marshmallowday and current repository admin/push
permissions were rechecked read-only through the GitHub plugin. Continue the
existing M06 branch rebel/m06-kernel-value-repair-20260927 from
`c975ad769a89e8baf627f2741d2f12974753cc51`: it contains the unaccepted
carried-value batch and its repairs. Main remains
`6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`.

## Actual same-SHA Actions

| Workflow | Run | Job | Result |
|---|---:|---:|---|
| CI | [36312895797](https://github.com/marshmallowday/leanrebel/actions/runs/36312895797) | 108602093569 | umbrella import failed |
| ReBeL checks | [36312895880](https://github.com/marshmallowday/leanrebel/actions/runs/36312895880) | 108602093907 | umbrella import failed |
| M06 targeted | [36312895850](https://github.com/marshmallowday/leanrebel/actions/runs/36312895850) | 108602093603 | target builds passed; joint audit import failed |
| source inventory | [36312895889](https://github.com/marshmallowday/leanrebel/actions/runs/36312895889) | 108602093780 | success |

All runs completed on the exact c975ad7 SHA. Complete decoded job logs and
artifact metadata were read. The targeted build succeeded (3483 jobs), and
the audit's module build also succeeded (3475 jobs). In particular the previous
concrete two-stage fuel mismatch is fixed. The generated joint audit import
then failed before printing the transitive axiom records.

CI and ReBeL checks fail while building GameTheory.Analysis.ReBeL. Both
report that PBSCarriedValue's import cannot be merged because the environment
already contains GameTheory.ReBeL.carriedMemoryStep_selected_expect from
CFRDRefreshMix. This is a shared declaration collision, not an axiom failure.

ReBeL checks also passed static architecture, 160 Python tests (9.031 seconds),
and the rational Lean solver/runtime check. Inventory passed 160 tests
(9.575 seconds). LIBRARY_LINES_OVER_100=0 and TRANSPORT_ANALYSIS_SOURCE=0.
Full normal/slow lint and complete transitive axiom audits are not accepted.
The source snapshot job 108602093761 succeeded.

## Repair and scope

Rename only the new PBSCarriedValue declaration and its local caller to
carriedMemoryStep_selected_late_expect, and align the current batch document
and owner ledger. CFRDRefreshMix keeps its existing public name.

The two results are closely related but have different stopped-branch forms:
the older theorem retains stage.fuel+remaining; the new theorem normalizes a
stopped stage directly to remaining. No mathematical statement or proof body
changes beyond the declaration/caller identifier. No workflow, audit, target,
test, solver or bound changes.

All eleven declarations in the new core module were compared with the
5062 declaration names in the previously accepted fa95a3d global audit log
(job 108575283035). Only this name collided. The seven added opponent-transport
declarations and one added kernel-value declaration have no collisions in
that baseline. The branch's fa95a3d..c975ad7 changed-source patches identify the
two code occurrences and current documentation references. Historical snapshots
and failure reports keep their original names. These are source/name checks,
not a substitute for compiling or auditing the new SHA.

## Artifacts

- m06-targeted-c975ad769a89e8baf627f2741d2f12974753cc51: artifact 10928984114; sha256:a640d755f4ee8f15d0506317adb3975fed823bde1e76baafdeb7cea53e48329e
- rebel-validation-c975ad769a89e8baf627f2741d2f12974753cc51: artifact 10929987388; sha256:56c3f7890886abfce50d513e2d24a7438f32c144429c4ddabf8c3e7b8001d34a
- rebel-source-c975ad769a89e8baf627f2741d2f12974753cc51: artifact 10928794047; sha256:568f8d304a333d12f2a55a5b28317aad3753a26a4591c992561cc6c60c7e16d2

Binary archives were not downloaded. Evidence above comes from complete
decoded job logs. CI and inventory report no artifacts.

## Acceptance boundary

Retain 156 targets, 118 targeted/261 global modules and 160 tests.
Current CI push, ReBeL main/rebel/** push and targeted rebel/m06* plus matching
Lean path triggers were re-read. The successor needs all three distinct runs
on its own SHA. Do not use this partial build success or old fa95a3d acceptance
as new-source acceptance. Remaining semantic work is unchanged in
M06-carried-value-batch.md. M06 is incomplete.
