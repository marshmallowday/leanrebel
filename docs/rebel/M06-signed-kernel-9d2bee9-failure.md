# M06 signed-kernel feedback at 9d2bee9

Continue the existing M06 branch rebel/m06-kernel-value-repair-20260927 from
the re-read HEAD `9d2bee9370e25a85fe384f8d3d095afc6be1c6c3`.
The connected account marshmallowday and current repository admin/push
permissions were rechecked using read-only plugin operations.
Main remains 6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098.
The branch contains the current unaccepted batch and is the appropriate base.

## Exact-SHA Actions evidence

| Workflow | Run | Job | Result |
|---|---:|---:|---|
| CI | [36319333902](https://github.com/marshmallowday/leanrebel/actions/runs/36319333902) | 108620001530 | compilation failure |
| ReBeL checks | [36319333885](https://github.com/marshmallowday/leanrebel/actions/runs/36319333885) | 108620001622 | compilation failure |
| M06 targeted | [36319333905](https://github.com/marshmallowday/leanrebel/actions/runs/36319333905) | 108620001489 | compilation failure |
| source inventory | [36319333863](https://github.com/marshmallowday/leanrebel/actions/runs/36319333863) | 108620001505 | success |

All runs completed with the exact 9d2bee9 head SHA. Complete decoded logs for
the four jobs and artifact metadata were inspected. All three Lean runs fail
at TypeBeliefSlice.lean:188 in ofJointBelief_kernel_law. There are no other
reported source diagnostics; downstream modules depending on this proof
were blocked, so they are not accepted.

ReBeL checks passed static architecture, 164 Python tests in 8.268 seconds
and the rational Lean solver/runtime check. Inventory passed 164 tests in
9.365 seconds. LIBRARY_LINES_OVER_100=0 and TRANSPORT_ANALYSIS_SOURCE=0.
The source snapshot job 108620001490 succeeded.
Complete build, normal/slow lint and transitive axioms remain unverified.

## Cause and precise repair

The proof produced positive support in the set
`{h | memory.typeAt (M.infoOf who h.trace) = type}`.
The final simp step reduced conditionedKernel but did not select the positive
condOnFibre branch, whose predicate is written as the preimage of a singleton.

Supply a separately typed positiveFibre witness for that preimage, then use
explicit dependent-if rewrites and definitional reflexivity. This follows the
already accepted ofJointBelief_reconstruct proof in the same file.
The theorem statement, mathematical assumptions and conditioning semantics
are unchanged. No workflow, audit, test, target or specification changes.

## Artifact metadata

- m06-targeted-9d2bee9370e25a85fe384f8d3d095afc6be1c6c3: artifact 10931364850; sha256:05f4048e2123555a9b87af5700949d4655c1d4a323ae24eb7e2cfea7ceab7a1c
- rebel-validation-9d2bee9370e25a85fe384f8d3d095afc6be1c6c3: artifact 10932446951; sha256:1bcb3f934f007afe5987b3549357b2060a68c76e6b2c81b01f5cb397c67b9bd1
- rebel-source-9d2bee9370e25a85fe384f8d3d095afc6be1c6c3: artifact 10931597604; sha256:fd076609dbdeb7451ad5a25575632760b69876b20fd71d026080ea0e695b1e73

Binary archives were not downloaded. Claims above rely on complete decoded
job logs. CI and inventory report no artifacts.

## Acceptance boundary

The repaired SHA requires its own distinct CI, ReBeL checks and M06 targeted
runs. Their current push/branch/path triggers were reread and remain unchanged.
Retain 156 targets, 118 targeted/261 global modules and 164 Python tests.
Do not transfer d771e88 acceptance to this changed source. The signed-kernel
batch and original M06 obligations remain incomplete as described in
M06-signed-kernel-batch.md.
