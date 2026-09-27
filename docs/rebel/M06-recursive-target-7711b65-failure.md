# Recursive training batch: 7711b65 validation failure and proof-style repair

Branch: rebel/m06-kernel-value-repair-20260927.
Failed source and repair parent: 7711b65f98851187eef0e05c66b5ba569e03ccf0.
Read-only GitHub plugin checks reconfirmed marshmallowday/admin and this branch
HEAD. Main remains 6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098. The existing branch
is continued because it contains the complete pending recursive-target batch.
No other update is overwritten.

## Complete job evidence

All runs below reported the failed source SHA. Complete decoded job logs and
artifact metadata were read through the plugin.

| Workflow | Run | Job | Result |
| --- | --- | --- | --- |
| CI | [36355626240](https://github.com/marshmallowday/leanrebel/actions/runs/36355626240) | 108722665278 | failure |
| ReBeL checks | [36355626242](https://github.com/marshmallowday/leanrebel/actions/runs/36355626242) | 108722665293 | failure |
| M06 targeted | [36355626189](https://github.com/marshmallowday/leanrebel/actions/runs/36355626189) | 108722665109 | failure |
| Source inventory | [36355626233](https://github.com/marshmallowday/leanrebel/actions/runs/36355626233) | 108722665255 | success |

Each compiler log has the same single source diagnostic:
PBSRecursiveValueTarget.lean:108:6, style.haveILetI: the goal is a proposition,
so a local let instance is preferred over letI. The error occurs inside
pbsRecursiveTargetRound_error. The module is not accepted merely because its
other declarations produced no diagnostics.

PBSComposedValueTarget compiled in all three jobs. ReBeL checks also recorded
LIBRARY_LINES_OVER_100=0, TRANSPORT_ANALYSIS_SOURCE=0, RATIONAL_RUNTIME_PASS and
185 Python tests in 9.088 seconds. Inventory ran 185 tests in 10.097 seconds,
including the four new recursive target controls. The downstream example
module, full umbrella build and complete normal/slow lint and transitive
axiom records were not reached successfully.

Artifact metadata:
- Targeted 10943911477, sha256:a30457427f4a0c8113aed2efbb312a4164935f1af59c1447380fd29c724e8879.
- Global 10944347965, sha256:66e734ccddbdfbea528a80d2e428c0ff1e114e200a0692211c155264d5528967.
- Source snapshot 10944460091, sha256:7b28e7ef0c6667588014a88ee2da42d39481f3f40afccbc6e3a35371a0f135e5.
CI and inventory exposed no artifact. Snapshot job 108722665471 succeeded.
Binary archives were not downloaded; diagnostic evidence is from complete logs.

## Repair and scope

Change only the local proof instance at line 108 from letI to let _.
The two computational definitions retain letI: their goals are data, not
propositions. This uses the existing accepted PBSRecursiveDepth proof pattern.
Definitions, mathematical statements, premises, algorithms, examples, tests,
workflows and audit criteria are unchanged. The linter is not disabled.

The repair retains 163 build targets, 125 targeted/267 global audit modules
and 185 Python tests. Exact repaired-source Actions are still required.
107bbaa's accepted logs do not validate this source. P-CFRD-TARGET remains
pinned to unchanged accepted source; the new recursive integration and M06
as a whole remain incomplete. See M06-recursive-target-batch.md for scope.
