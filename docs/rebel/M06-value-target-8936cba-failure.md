# M06 root value-target example: 8936cba failure and repair

Failed source: 8936cbaf98c0cc7980ae97946109e15ff6f46d96.
Working branch: rebel/m06-kernel-value-repair-20260927.
Read-only GitHub preflight reconfirmed marshmallowday, repository admin/push,
unchanged working HEAD and main 6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098.
Continue the same branch from this actual failed source.

## Exact-SHA evidence

| Workflow | Run / job | Result |
| --- | --- | --- |
| CI | [36337366569 / 108670669688](https://github.com/marshmallowday/leanrebel/actions/runs/36337366569) | example build failure |
| ReBeL checks | [36337366533 / 108670669698](https://github.com/marshmallowday/leanrebel/actions/runs/36337366533) | example build failure |
| M06 targeted | [36337366542 / 108670669790](https://github.com/marshmallowday/leanrebel/actions/runs/36337366542) | example build failure |
| Source inventory | [36337366537 / 108670669853](https://github.com/marshmallowday/leanrebel/actions/runs/36337366537) | success |

Complete decoded logs were fetched through the GitHub plugin. All three
compiler jobs report exactly the same remaining error:
Examples/CFRDValueTarget.lean:32:8 cannot synthesize
(who : Fin 2) -> (info : (pbsRootFullInformation M roots).InfoState who) ->
Fintype ((pbsRootFullInformation M roots).Choice who info).
The example explicitly uses the generic cfrDDepthExactTarget comparator;
the local rooted-menu instances inside the parent module are not exported
to this consumer.

CFRDValueTarget itself compiled successfully in all three jobs, including
the explicit conditional-law rewrite, hrecall binders, arithmetic update
and terminal-backup proof. Targeted reports its build at step 3437/3485
(4.1s), checks at 3472/3521 (4.4s). This clears the previous fc21b53 causes,
but does not count as full lint or axiom acceptance.

ReBeL checks passed LIBRARY_LINES_OVER_100=0, TRANSPORT_ANALYSIS_SOURCE=0,
ledger/inventory, rational runtime, and 176 Python tests in 9.013s.
Inventory independently passed 176 tests in 9.837s and tracked-file
cleanliness. The target/full transitive axiom and complete lint gates did
not finish successfully because the example failed to build.

Artifact metadata inspected: targeted 10937613056
(sha256:b1119a22434f04268fd22e8c116d575da4d30609691bfeb2e84230e1d9e95135),
global validation 10937737871
(sha256:889f97254bcffcf8d1ebb89c305136736a7e77ba313ea553f8f56075d22ec4d4),
source snapshot 10937288812
(sha256:71a6efd1ddeda78258e768ff043711a00e946d831e631566a3ca46c42255cd18).
Snapshot job 108670669791 succeeded. CI and inventory had no artifacts.
Binary archives were not downloaded; decoded logs supply the diagnostics.

## Consumer repair

The example now supplies local rooted choice Fintype and rooted full-AOH
DecidableEq instances, using classical subtype enumeration and equality,
matching the existing parent module's construction. This provides the
generic comparator's elaboration requirements without adding mathematical
assumptions, changing its target vector, weakening a theorem, or changing
the example's game, noise or finite iteration count.

The library core, workflows, all audit gates, tests and frontier journal
anchors are unchanged. The repaired example and complete imports still
require their own exact-SHA Actions: 158 targets, 120 targeted / 263 global
audit modules and 176 Python tests. e123cb8 remains the last fully accepted
source for the pre-target dependency batch; its results cannot validate
this repair. After this repair phase passes, resume large related batches.
M06 and the root-target batch remain incomplete.
