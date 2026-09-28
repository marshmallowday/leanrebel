# Stopped-mass batch: exact 4b40364 failure and repair review

Selected work branch: rebel/m06-kernel-value-repair-20260927.
Repair parent: 4b40364ffe22ddea0d04d7c6f6db79a390f721f0.
The plugin account remains marshmallowday with admin/push permission.
Default main was checked separately at 6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098.
Continue this branch because these failures belong to its stopped-mass batch;
the last fully accepted dependency source is 133dc24, not the failed candidate.

## Exact-source evidence

| Workflow | Run | Job | Result |
| --- | --- | --- | --- |
| [CI](https://github.com/marshmallowday/leanrebel/actions/runs/36397392172) | 36397392172 | 108846912244 | failure |
| [ReBeL checks](https://github.com/marshmallowday/leanrebel/actions/runs/36397392250) | 36397392250 | 108846912325 | failure |
| [M06 targeted](https://github.com/marshmallowday/leanrebel/actions/runs/36397392185) | 36397392185 | 108846912525 | failure |
| [Source inventory](https://github.com/marshmallowday/leanrebel/actions/runs/36397392214) | 36397392214 | 108846912779 | success |

All four head_sha values equal the repair parent. Complete decoded job logs were
read through the GitHub plugin. The three compiler diagnostic blocks are identical.
FinDistConditioningError compiled in 2.8s / 2.3s / 1.7s respectively.
Checks reported LIBRARY_LINES_OVER_100=0, TRANSPORT_ANALYSIS_SOURCE=0,
RATIONAL_RUNTIME_PASS and 205 Python tests in 9.005s. Inventory passed 205 tests
in 8.843s. Downstream examples, full build, complete normal/slow lint and full
transitive axiom records remain unaccepted.

Artifact metadata was inspected: targeted 10958553986, global 10959733018,
source 10959340410. CI and inventory had no artifacts. The checks source-snapshot
job 108846912656 succeeded. Binary ZIP contents were not read; the complete
decoded job logs provide the diagnostic evidence.

## Complete shared compiler diagnostics

```text
error: GameTheory/Analysis/ReBeL/CFRDStoredChildDefect.lean:37:8: Application type mismatch: The argument
  possible
has type
  PublicBelief.Possible.{0, us, ua, uk, uq, max (max ua uk) uq} ((fullInformation M).runBehavioral trunk cut) obs
but is expected to have type
  PublicBelief.Possible.{0, us, ua, uk, uq, up} ((fullInformation M).runBehavioral trunk cut) obs
in the application
  PublicBelief.condition ((fullInformation M).runBehavioral trunk cut) obs possible
error: GameTheory/Analysis/ReBeL/CFRDStoredChildDefect.lean:55:8: Application type mismatch: The argument
  cfrDFactualChildPossible_public M trunk cut remaining obs possible
has type
  PublicBelief.Possible.{0, us, ua, uk, uq, max (max ua uk) uq} ((fullInformation M).runBehavioral trunk cut) obs
but is expected to have type
  PublicBelief.Possible.{0, us, ua, uk, uq, up} ((fullInformation M).runBehavioral trunk cut) obs
in the application
  PublicBelief.condition ((fullInformation M).runBehavioral trunk cut) obs ⋯
error: GameTheory/Analysis/ReBeL/CFRDStoredChildDefect.lean:78:34: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
error: GameTheory/Analysis/ReBeL/CFRDStoredChildDefect.lean:114:8: Application type mismatch: The argument
  cfrDFactualChildPossible_public M trunk cut remaining obs possible
has type
  PublicBelief.Possible.{0, us, ua, uk, uq, max (max ua uk) uq} ((fullInformation M).runBehavioral trunk cut) obs
but is expected to have type
  PublicBelief.Possible.{0, us, ua, uk, uq, up} ((fullInformation M).runBehavioral trunk cut) obs
in the application
  PublicBelief.condition ((fullInformation M).runBehavioral trunk cut) obs ⋯
error: GameTheory/Analysis/ReBeL/CFRDStoredChildDefect.lean:143:8: Application type mismatch: The argument
  cfrDFactualChildPossible_public M trunk cut remaining obs possible
has type
  PublicBelief.Possible.{0, us, ua, uk, uq, max (max ua uk) uq} ((fullInformation M).runBehavioral trunk cut) obs
but is expected to have type
  PublicBelief.Possible.{0, us, ua, uk, uq, up} ((fullInformation M).runBehavioral trunk cut) obs
in the application
  PublicBelief.condition ((fullInformation M).runBehavioral trunk cut) obs ⋯
error: GameTheory/Analysis/ReBeL/CFRDStoredChildDefect.lean:164:8: declaration uses `sorry`
error: GameTheory/Analysis/ReBeL/CFRDStoredChildDefect.lean:190:8: declaration uses `sorry`
```

## Repair and precommit type review

The earlier review explicitly typed Possible and publicTrace but missed the
implicit S of PublicBelief.condition. Its definition in GameTheory/ReBeL/Belief.lean
requires Possible (S := S) and returns PublicBelief S observations. The original
information-state universe up is independent of the full AOH universe
max (max ua uk) uq; the public signal list alone does not fix this implicit S.

Every condition constructor in CFRDStoredChildDefect (six, including both
downstream composed-round statements) now specifies
S := (fullInformation M).toInfoSignals. Both concrete example constructors
specify S := (model fullPrior).toInfoSignals. The deprecated Set.mem_setOf_eq
is replaced by the compiler-recommended Set.mem_ofPred_eq. No universe is
specialized, no semantic premise is added, and no algorithm definition changes.
The two downstream sorry diagnostics are failed dependency elaboration, not
literal placeholders in these sources; no warning is disabled.

The complete core and example consumers were reviewed, not only the four
locations diagnosed first:

- cfrDFactualChildPossible_public and cfrDFactualChildBelief both use the same
  full-information signal carrier and trunk law. Their actual signatures were
  reread in CFRDStoredChild and CFRDFactualChild.
- carriedBeliefUpdate/continuationLaw use fullInformation M; condition? after
  rewriting the prefix law now has exactly the explicit constructor's S.
- Conditional expectation/support proofs use the same outer public event,
  inner live-public event, law and positivity witnesses. The compiled
  FinDistConditioningError signature takes outer then inner; the bound remains
  public-minus-live in absolute value, with stopped/public mass ratio.
- cfrDComposedNextState retains state.history-dependent prior indexing and the
  new history's full public trace. The generic memory carrier K and future
  Outcome remain independently polymorphic.
- Both actual noisy example consumers retain their explicit PBSChildSolve
  and trunk Profile aliases, canonical finite History/Choice instances,
  classical InfoState equality, cut=2, remaining=1, child schedule [1], and
  the same noise/round/fallback/payoff. Their reducedModel/full model types
  match the previously accepted PBSStoredChildReplay consumers.
- The future-error example retains the same continuation on both posterior laws.
  Its zero specialization rewrites the stopped-mass numerator after the local
  let expressions have been reduced; it does not change the solver's kernel.
- All edited Lean lines are at most 100 characters; no new declarations,
  untyped solver aliases, placeholders, or axiom assumptions were introduced.

This is static source/signature review, not compiler execution. Actual
elaboration, full lint and transitive axiom acceptance require the new SHA's
GitHub Actions. Tests, workflows, audit thresholds and all 175 build targets /
137 targeted / 278 global modules are unchanged. The frozen coverage.json blob
remains 2fc8cc9ad6607d61bfe397707fb96ac322fbb800. No original M06 obligation is
promoted: changed solver kernels, root-wrapper configuration correspondence,
native-chain small losses and SEARCH-CFRD/SEARCH-ERROR/SAFE-THEOREM3 remain open.
