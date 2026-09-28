# Fixed-trace average limit: cc4ba60 feedback and repair

Branch: rebel/m06-kernel-value-repair-20260927.
Failed SHA: cc4ba60a4d934db97bde5cb95cfb6471a9b7e1ee.
Accepted baseline: 4de8c48f532575440c8159dfe15c96fc1c7180f0.
Chat baseline: 9457c198126f3c8b7cb1045bbed2e0053788636f.

Read-only plugin checks reconfirmed marshmallowday/admin with push permission,
the work HEAD above and default main
6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098. Continue the existing M06 branch:
its current failed batch is the intended unfinished work, not a branch chosen
by timestamp. All four workflow head_sha values match the failed SHA.

## Exact-source evidence

| Workflow | Run | Job | Result |
| --- | --- | --- | --- |
| CI | [36362617128](https://github.com/marshmallowday/leanrebel/actions/runs/36362617128) | 108742656006 | failure |
| ReBeL checks | [36362617131](https://github.com/marshmallowday/leanrebel/actions/runs/36362617131) | 108742656627 | failure |
| M06 targeted | [36362617158](https://github.com/marshmallowday/leanrebel/actions/runs/36362617158) | 108742656182 | failure |
| Source inventory | [36362617164](https://github.com/marshmallowday/leanrebel/actions/runs/36362617164) | 108742656037 | success |

Complete decoded logs were read through the plugin. All three compiler jobs
report the same sole Lean diagnostic at CFRDAverageLimit.lean:126:19.
The applied add_le_add_left budget expression adds the unchanged term on
the wrong side for this goal: Lean displays budget + expectedUtility, but
the transitivity step requires expectedUtility + budget.
The existing inequality is valid; its application has the wrong orientation.

The repair uses add_le_add le_rfl budget to keep the expected utility on the
left and enlarge only the right summand. The same expression occurs twice
in PBSAverageLimit (the finite-child and composed-parent consumers), whose
build was blocked upstream. Those two latent occurrences are repaired in the
same commit. No definition, mathematical statement, assumption, workflow,
audit criterion or test is changed.

Checks reports LIBRARY_LINES_OVER_100=0, TRANSPORT_ANALYSIS_SOURCE=0,
RATIONAL_RUNTIME_PASS and 190 Python tests in 9.000 seconds.
Inventory reports 190 tests in 6.334 seconds. The downstream PBS/example build,
umbrella build and complete normal/slow lint/transitive axiom audit remain
unverified. Neither these partial results nor the old 4de8c48 successes
accept the repaired source. Validation takes place only in GitHub Actions;
no local Lean or Python execution occurred.

Artifact metadata inspected (no binary archive download):

- Target 10946431866, sha256:78884f76816731c45404a9217acea56d23c296aa43de74801cb30d6f87b3d3bf.
- Global 10945789647, sha256:fc2d9992e2ba3e8d44e360e8a42e03b04da1c687d5d8709b1b8ed4fff878c7a6.
- Snapshot 10945439235, sha256:dfef193cc4ff718b7d99d736b6b59dbb46711efadcf16500a33745943de30141.

Snapshot job 108742656031 succeeded. CI and inventory had no artifacts.
The failed core blobs were 52ed384e465ec045869e02e72a5a3dad0c7e1e1e
(CFRDAverageLimit) and f0eba9725c303d901f860ad24887562b963ebccb
(PBSAverageLimit). The example remains e652ad88cebafd6a8631da7597c427e575821231.

## Remaining gates

Keep 166 build targets, 128 targeted / 270 global audit modules and 190 tests.
P-CFRD-AVERAGE remains pending until repaired-source Actions and semantic
review, including fixed-trace scope and the accepted root-vector arithmetic.
SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 are not closed by this repair.
The nonzero noise/child floor, additive finite-T remainder and distinction
between Nash-error convergence and final-iterate/profile convergence remain.

Push triggers were re-read at cc4ba60: CI handles push; ReBeL checks and
inventory match rebel/**; targeted matches rebel/m06* and these changed Lean
paths. No workflow change or manual dispatch is needed. After a single
Git Data commit, verify separate runs on its exact SHA, then schedule the
current chat once 50 minutes after ref update in Asia/Tokyo.
