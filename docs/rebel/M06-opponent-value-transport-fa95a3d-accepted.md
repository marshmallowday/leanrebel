# M06 changed-opponent repair accepted at fa95a3d

Checked via the GitHub plugin on 2026-09-27, after the scheduled follow-up.
Validated source: fa95a3d06b2061b18fa678518c2adf0531650377.
Work branch: rebel/m06-kernel-value-repair-20260927.
Original chat baseline: 9457c198126f3c8b7cb1045bbed2e0053788636f.
Default main remains 6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098.
Login marshmallowday, collaborator admin and repository push=true were rechecked.

| Workflow | Run | Job | Result |
| --- | --- | --- | --- |
| CI | [36303420528](https://github.com/marshmallowday/leanrebel/actions/runs/36303420528) | 108575282589 | success |
| ReBeL checks | [36303420514](https://github.com/marshmallowday/leanrebel/actions/runs/36303420514) | 108575283035 | success |
| M06 targeted proof feedback | [36303420502](https://github.com/marshmallowday/leanrebel/actions/runs/36303420502) | 108575282842 | success |
| ReBeL source inventory | [36303420513](https://github.com/marshmallowday/leanrebel/actions/runs/36303420513) | 108575282866 | success |

All four run head_sha fields match this exact commit. Complete decoded job logs
were fetched and inspected. Target build retains 154 names. The targeted audit
reports 1912 declarations and 116 modules; global audit reports 5062 declarations
and 259 modules. Every multiline transitive-axiom record was parsed: only
propext, Classical.choice and Quot.sound occur. All 116 explicit targeted lint
pass markers are present. Normal and slow lint are included by the existing
auditor. Full CI build, full-library lint, source/inventory, Phase 1/2/3
architecture and tracked-file cleanliness gates passed. Pinned Lean is 4.33.1.
The ReBeL job and source inventory both executed 153 Python tests successfully.
This includes the four changed-opponent Fraction controls.

Artifacts were inspected as metadata; binary archives were not downloaded:
- CI 10926876038, sha256 a653c61404469a0059c5fee347aff2dfdd982fe630b8c4cb800307afc690bda8.
- Target 10926816399, sha256 8a27db782ccc6570b4fc9a94343313ccec4ba53dfcf433df11dc1272c68cfa51.
- Global 10926343934, sha256 a0324d5a16300dcdbd1c199899533a6ac4c2d975284e4a04d32147bf2be17dfa.
- Source 10926457178, sha256 6eaa8f542a3d40a712abca79083279e9f65040afc837dab3abc3977673399493.
- Inventory produced no artifact.

Semantic review: PBSKernelValueTransport compares the same own response under
both opponent profiles and root laws. The optimum comparison charges both
constructed maximizers, and the gap also charges the retained own response.
PBSDepthKernelGap preserves the native correlated conditional query and does
not divide its already averaged new cost by the event probability again.
The primitive source costs are computed but not asserted small. Actual noisy
parent and independently constructed child controls compile under these same
audits. This accepts the changed-opponent dependency, not M06 or Theorem 3.

The historical coverage.json is exactly blob
2fc8cc9ad6607d61bfe397707fb96ac322fbb800, as required by accepted append-only
M05 journals. Future M06 progress must not rewrite that frozen base.
