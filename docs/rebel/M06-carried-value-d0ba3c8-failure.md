# M06 carried-value example feedback at d0ba3c8

This records actual GitHub Actions evidence for
`d0ba3c83e2e6771d998bc28ff99edb1e3980c5d4`, not acceptance of its successor.
The connected account and current admin/push permissions were rechecked.
The existing M06 branch remains the correct continuation: it contains the
ed2fad carried-value batch and its d0 proof/architecture repair. Main remains
`6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`.

## Exact-SHA results

| Workflow | Run | Job | Result |
|---|---:|---:|---|
| CI | [36309904959](https://github.com/marshmallowday/leanrebel/actions/runs/36309904959) | 108593701574 | example compilation failed |
| ReBeL checks | [36309904962](https://github.com/marshmallowday/leanrebel/actions/runs/36309904962) | 108593701863 | architecture and Python passed; example compilation failed |
| M06 targeted | [36309904952](https://github.com/marshmallowday/leanrebel/actions/runs/36309904952) | 108593701634 | example compilation failed |
| source inventory | [36309904951](https://github.com/marshmallowday/leanrebel/actions/runs/36309904951) | 108593701481 | success, 160 tests |

All listed runs have the exact d0ba3c8 head SHA. Complete decoded job logs and
artifact metadata were inspected. The ReBeL source snapshot job 108593701756
succeeded. The diagnostics log reports LIBRARY_LINES_OVER_100=0 and
TRANSPORT_ANALYSIS_SOURCE=0, and 160 tests in 8.696 seconds. Inventory reports
160 tests in 9.797 seconds.

PBSOpponentModelTransport, PBSKernelValueTransport, PBSCarriedValue and
PBSDepthKernelGap compile in the target/global logs. The previous unused simp
argument and Analysis source-transport failures are resolved. Full postbuild
lint and transitive axiom audits remain unverified because the example fails.

## Common compiler failure and repair

All three Lean runs report a type mismatch at
GameTheory/Analysis/ReBeL/Examples/PBSCarriedValue.lean:36.
After simplification, the generic signed loss bound still contains
`carriedResolveFuel M 0 depthControlStages`, while the concrete goal contains
`2`. The global schedule-fuel rewrite did not match under the local model alias.

The repair states the definitionally true equality locally:
`have totalFuel : carriedResolveFuel M 0 depthControlStages = 2 := rfl`,
then uses it in the existing `simpa only`. No theorem statement, model,
bound, implementation, test, workflow or audit budget changes.

## Artifact metadata

- Target artifact 10929180448:
  sha256:1041c54473112be4fee072fb03e645a934ad8f492f2e2c02817e92294ed1d3fa
- Global diagnostic artifact 10929256539:
  sha256:a931fb29dd7b5a2d15b1f589645461ca5ef5454d7faf9091f391b49b6e7d9401
- Source artifact 10928204979:
  sha256:d23f8fb3e952090348a6f586313a875e0544385e4af5f011d2de4141b64bca9c

Binary artifact archives were not downloaded; claims above derive from the
complete decoded job logs. CI and inventory have no artifacts.

## Acceptance boundary

The successor requires its own CI, ReBeL checks and M06 targeted results,
156 build targets, 118 targeted/261 global audit modules, full transitive
axiom output, normal/slow lint, architecture and 160 Python tests.
Do not transfer old fa95a3d acceptance to the carried-value batch.
M06 remains incomplete for the semantic obligations in
M06-carried-value-batch.md and the M06 owner ledger.
