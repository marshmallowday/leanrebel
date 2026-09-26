# M06 conditioned-query compiler repair

Continue on `rebel/m06-conditioned-query-20260925` from its actual latest head.
Initial implementation: `45664f4a6c8ea312ba7ba6cc2501cb71ba5fd3de`.
First parser repair: `0a0183233232566ac20527af7c4f37ee70be8945`.
M06 and Theorem 3 remain incomplete; no coverage acceptance is changed.

## Actual compiler loop

Initial targeted run `36152371154`, job `108128541644`, failed at a missing
closing parenthesis in the local actual-law expression. The 0a01832 repair
closes that expression after Prod.fst, preserving the intended statement.
Actual failure artifact `10872646142` was downloaded through the GitHub plugin:
ZIP SHA256 7739b8377ce03a05b67272686657ed515e31bf32b92e9532b2bc10d0e12e21ae;
log SHA256 c31890c3350ec62c7b59d989646d1d58ae4d3e6b124a60f4ea49e528755179e0.

Repaired-source target `36153218875`, job `108131386873`, then parsed the entire
helper but rejected applying mt directly to its set-subset theorem (line 104).
Actual artifact `10872816625` was downloaded through the plugin:
ZIP SHA256 8991b089a9466d0311dfbd8fbb3f064c0c984c0fbe1a4c6cf9907e49cfc2b2d1;
log SHA256 03fff4e00cf9b82e19781bcdc5eec10010f7a78cc9597e5cdbe0265d085141f7.
The current repair supplies the absent tag and supported-point argument
explicitly, then contradicts absence in the original support. It does not
change any statement, assumption, import, test or gate. Both logs identify
their exact source and Lean 4.33.1. All downstream compilation and subsequent
lint/axiom checks remain unaccepted until an actual successful run is read.

## Exact source and independent checks

Initial source artifact `10871968005` was downloaded through the plugin:
ZIP SHA256 fc83e8571a9257ad85ed3f09de2703bd6f51a4cc9b0bf6a0ff6fc465ed090ca7;
tar SHA256 41e771b196a92addc44398b5151f31d0b746c7b38ee78d6929537545ee69dffb.
Its embedded commit is 45664f4. All seven prepared source/test/registration
files match committed bytes. Toolchain/dependency pins, basic umbrella and
canonical coverage are unchanged. The previous STATUS is retained exactly.
All 92 Python tests were executed again on that exact export with warnings
as errors: SUCCESS. Test-log SHA256:
bb999bdaf179a43e6ac0cb643654e9e397e8b6da6fd1ee37a40570334e44028f.
All 3,054 inherited coverage/inventory items retain their original states.
These are structural and rational checks, not Lean kernel verification.

Predecessor 3cfc5e0 full CI `36149297382` / `108118771741` is SUCCESS, including
full build/lint, reuse signatures and all Phase 1/2/3 architecture/reachability
checks. Actual artifact `10871837192` was downloaded and inspected:
ZIP SHA256 fade4ba311eb58cb8135cb13c514c884eff703ddec7fd8ac00a250a8a1b5d062.
The embedded ci-source.txt identifies 3cfc5e0. ci-lint.log SHA256:
5aa67fbec0aae6c29d97705ab3e40119fd46f8e87be873322ebe5c677a060c35;
its complete public-library lint passes. All three architecture logs end in
VERIFIED=1. The Windows-only setup step was skipped on Linux as configured.
Parent all-ReBeL `36149297460` remained running at last observation. None of
this predecessor evidence validates the new conditioned-query modules.

## Next gate and scope

Read the exact branch-head targeted run first and repair every compiler or
lint error without weakening the mathematical statements. Require 107-module
supplemental normal/slow lint and complete transitive axiom output, then the
independent all-ReBeL and full CI. Pending results are not acceptance.
M06-conditioned-query.md remains the semantic review: fixed original kernels
and fixed average comparison opponents, actual event probability, retained
private seeds, impossible events excluded. Public-carried-PBS identification,
first-exit/event rates, changing-opponent/PBS value rates and independent
recursive re-solving safety remain open project obligations.

## 2026-09-26: history-map and downstream example repairs

The branch head before this repair was
`73596bd8c96d54ec8fb19528b61a416f89decf4d`. Its targeted run
[36154403503 / 108135311209](https://github.com/marshmallowday/leanrebel/actions/runs/36154403503/job/108135311209)
failed at PBSConditionedNativeGap.lean:74. Normalizing the tagged history
marginal left a FinDist.map of the explicit identity lambda, while the
sampling-law theorem had no map. The local mapHistory equality specializes
the existing FinDist.map_id to that lambda so simp can eliminate it.
The theorem statement and all assumptions are unchanged.

Commit `03f5beebc6d75109bf9b0166c083b0c9ed071f84` compiled the repaired
main module in [36209528942 / 108312987212](https://github.com/marshmallowday/leanrebel/actions/runs/36209528942/job/108312987212).
That run then exposed errors in its previously uncompiled example module.
Commit `259d8194cec5c4118dd9ee0c6ba9f90af01adcf7` makes tagged-atom
probabilities explicit before simplification, derives event mass through
expectation congruence, and enumerates the finite product before evaluation.
Its run [36209932361 / 108314162920](https://github.com/marshmallowday/leanrebel/actions/runs/36209932361/job/108314162920)
identified remaining event-decidability and redundant-simp issues.
Commit `6d111a4aa3060be10fa7e655d0dbfde13660cc7c` supplies classical
event decidability in the example and splits the equality predicate explicitly.

Only proof bodies in the main and example PBSConditionedNativeGap.lean files
changed. Definitions, theorem statements, assumptions, positive and negative
controls, imports, dependencies and validation gates are preserved. In
particular, the actual conditioning event still has positive mass, the sharp
factor-two example and impossible-event control remain, and no public-carried
PBS identification or changing-opponent guarantee has been claimed.

### Exact repair-source validation

Source: `6d111a4aa3060be10fa7e655d0dbfde13660cc7c`.
Lean: 4.33.1 (pinned commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6).

[M06 target 36210326495 / 108315289526](https://github.com/marshmallowday/leanrebel/actions/runs/36210326495/job/108315289526)
is SUCCESS. Its actual job log was read through the GitHub plugin:
the main and example modules build, all 107 supplemental modules pass the
configured normal/slow lint, and the transitive axiom audit passes for 1,669
declarations. The three conditioned-query modules contribute 12, 13 and 18
audited declarations respectively. The repaired history theorem has exactly
[propext, Classical.choice, Quot.sound]. The log ends with
EXACT_LEAF_VALIDATION_PASS modules=107.

[ReBeL checks 36210326388 / 108315430319](https://github.com/marshmallowday/leanrebel/actions/runs/36210326388/job/108315430319)
is SUCCESS: REBEL_VALIDATION_PASS modules=251 and
REBEL_AXIOM_AUDIT_PASS declarations=4848. All 92 Python tests pass with
warnings treated as errors; the independent rational runtime check reports
RATIONAL_RUNTIME_PASS. Static architecture and tracked-file cleanliness pass.

[Full CI 36210326436 / 108315428119](https://github.com/marshmallowday/leanrebel/actions/runs/36210326436/job/108315428119)
is SUCCESS: complete library build/lint, compiler-resolved reuse signatures,
all Phase 1/2/3 architecture/reachability checks and clean tracked files.
All three architecture logs report VERIFIED=1. The configured Windows-only
setup step is skipped on Linux.
[Source inventory 36210326380](https://github.com/marshmallowday/leanrebel/actions/runs/36210326380)
also succeeds. Actual full-CI and ReBeL job logs were read through the plugin.

The following documentation-only checkpoint records these exact-source results
and the user's M07 onward branch policy. It does not change the compiled code,
its validation configuration, or original coverage acceptance states.

This is evidence for the compiler repair and its existing finite-law scope,
not acceptance of M06 or paper Theorem 3. The four original M06 obligations
remain pending.
