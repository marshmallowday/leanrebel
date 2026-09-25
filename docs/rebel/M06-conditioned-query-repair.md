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
