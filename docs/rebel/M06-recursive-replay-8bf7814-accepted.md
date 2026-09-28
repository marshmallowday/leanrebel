# Recursive replay acceptance at 8bf7814

Commit: 8bf78145c843a82580d89322bef13603434fddb9.
Branch: rebel/m06-kernel-value-repair-20260927.
All four runs report exactly this head SHA and completed/success.

| Workflow | Run | Job |
| --- | --- | --- |
| CI | [36370397855](https://github.com/marshmallowday/leanrebel/actions/runs/36370397855) | 108765320992 |
| ReBeL checks | [36370397903](https://github.com/marshmallowday/leanrebel/actions/runs/36370397903) | 108765321056 |
| M06 targeted | [36370397856](https://github.com/marshmallowday/leanrebel/actions/runs/36370397856) | 108765321127 |
| Source inventory | [36370397861](https://github.com/marshmallowday/leanrebel/actions/runs/36370397861) | 108765321012 |

Complete decoded logs were read through the GitHub plugin. All 2157 targeted
and 5298 global unique transitive axiom records were parsed, including multiline
records, with exactly matching record-start counts. Every list contains only
propext, Classical.choice and Quot.sound, or is empty. All 131 targeted and
273 global normal/slow module lint passes were checked.

CI full build completed 4298 jobs, lint build 4068, repository lint and all
three architecture VERIFIED checks passed. LIBRARY_LINES_OVER_100 and
TRANSPORT_ANALYSIS_SOURCE are zero. Rational runtime passed. ReBeL checks
ran 195 Python tests in 9.709 seconds; inventory ran 195 in 8.686 seconds,
both OK. The manifest contains 169 build targets.

Artifact metadata: CI10949486455, global10949493944, targeted10949083500,
source10949027883 (snapshot job108765321237); inventory has no artifacts.
Archive contents were not downloaded; complete axiom evidence was in logs.

Accepted dependency sources:
- PBSRecursiveReplay.lean: 612e9e4294131788601fb4dfdd5252593f38037d
- PBSRecursiveCarriedReplay.lean: ddae2a04aa37892550c4c8e49980c58d62f44984
- Examples/PBSRecursiveReplay.lean: 03043dd78df47c259bdbe27a33dfe6befa675564
- test_recursive_replay.py: 5875da8154fd25bb2d0cff6d7773e94d1f35f0cc

The semantic scope in M06-recursive-replay-batch.md is retained: replay of
the same computation on supported roots, explicit unsupported probability,
actual native conditional private-profile/model-posterior coupling, and the
same draw through stage plus late fuel. Arbitrary independently recomputed
policies do not acquire zero loss from Nash accuracy. This is dependency
acceptance, not SEARCH-CFRD/SEARCH-ERROR/SAFE-THEOREM3 or M06 completion.
New stored-child sources require their own exact-SHA validation.
