# Stored-child consumer elaboration failure at 376b118

Source 376b118d0b87c2ef84d3dde7d1cb90c20b7f72a9 on
rebel/m06-kernel-value-repair-20260927 was re-read before repair.
Plugin identity marshmallowday has admin/push access. Default main remains
6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098. Continue the current unfinished
M06 branch without modifying main or creating a PR.

## Exact-source Actions

| Workflow | Run / job | Result |
| --- | --- | --- |
| CI | [36382191159](https://github.com/marshmallowday/leanrebel/actions/runs/36382191159) / 108800075258 | build failed |
| ReBeL checks | [36382191075](https://github.com/marshmallowday/leanrebel/actions/runs/36382191075) / 108800074801 | build failed |
| M06 targeted | [36382191142](https://github.com/marshmallowday/leanrebel/actions/runs/36382191142) / 108800074913 | build failed |
| Source inventory | [36382190987](https://github.com/marshmallowday/leanrebel/actions/runs/36382190987) / 108800074317 | success |

All head SHAs match. Complete decoded logs were read. CFRDStoredChild compiles
in all three jobs (CI 2.7s, checks 2.5s, targeted 3.2s): the original/full
public-trace and reserved-binder repairs have passed this compilation gate.
This does not imply complete normal/slow lint or axiom acceptance.

The next module, PBSStoredChildReplay, times out at the same three statement
locations in every job. Each is the possible proof passed to factual-child
construction after locally aliasing the recursive solver and trunk.

Checks passed LIBRARY_LINES_OVER_100=0, TRANSPORT_ANALYSIS_SOURCE=0,
RATIONAL_RUNTIME_PASS and 200 Python tests in 8.509s. Inventory passed 200
tests in 8.230s. Full downstream build, complete lint and axiom audit remain
unverified.

Artifact metadata was inspected, not claimed as extracted archives:
target 10953208535, sha256 90c0ec0c8f5a481994b181ff338c894d6f16c8b55fddee281eaf405f3009ff7f;
global 10952798670, sha256 2fa8cf7ff139c89052873854ff423ff5c3db040981ea4190fecd04bd0e65a11c;
source 10952668893, sha256 4a2e6fd0e97a6a3827848fb87089f970963540b9e5103661422104c68dab360f.
Snapshot job 108800075072 succeeded. CI/inventory list no artifacts.

## Combined repair

The diagnostic locations point to elaborating the untyped local solver alias
against an observation-polymorphic PBSChildSolve argument. Give the three
solver aliases the expected PBSChildSolve M type before elaborating their
recursive definition. Also give each trunk its behavioral-profile type.
This keeps the implicit observation binder available in the expected type
instead of relying on inference through the large recursive computation.

Apply the same explicit types to both not-yet-reached concrete example
consumers. This is a combined elaboration repair, with the exact same solver,
arguments, belief support, mass-scaled target and conclusions. The proposed
performance fix still requires measurement by the new source's Actions.

No heartbeat limit is increased, no audit rule or workflow is weakened, and no
semantic hypothesis is added. Existing CFRDStoredChild source, tests,
172 targets and 134 targeted/276 global audit modules remain unchanged.
The repair and evidence are one commit; no local Lean/Python execution occurred.

## Full compiler diagnostic block

```text
error: GameTheory/Analysis/ReBeL/PBSStoredChildReplay.lean:50:50: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
error: GameTheory/Analysis/ReBeL/PBSStoredChildReplay.lean:93:50: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
error: GameTheory/Analysis/ReBeL/PBSStoredChildReplay.lean:137:50: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

The new source needs its own complete Actions validation. Previous full
acceptance at 8bf7814 is not validation of this repaired consumer.
M06 and its outstanding safety/source obligations remain incomplete.
