# Stored-child batch failure at ad3b6bc

Source: ad3b6bcc94ba8f5f44d418a2d920e9651d722645.
Branch: rebel/m06-kernel-value-repair-20260927.
The branch and main were re-read before repair; main remains
6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098. Plugin login marshmallowday has
admin/push permission. The existing M06 branch contains the unfinished batch,
so the repair continues its current HEAD without changing main or making a PR.

## Exact-source observations

| Workflow | Run / job | Result |
| --- | --- | --- |
| CI | [36374785262](https://github.com/marshmallowday/leanrebel/actions/runs/36374785262) / 108778283990 | build failed |
| ReBeL checks | [36374785236](https://github.com/marshmallowday/leanrebel/actions/runs/36374785236) / 108778283941 | build failed |
| M06 targeted | [36374785220](https://github.com/marshmallowday/leanrebel/actions/runs/36374785220) / 108778283970 | build failed |
| Source inventory | [36374785218](https://github.com/marshmallowday/leanrebel/actions/runs/36374785218) / 108778283858 | success |

All four runs report this exact head SHA. Complete decoded job logs were read;
the three compiler jobs have the same seven diagnostics in CFRDStoredChild.
No diagnostic was taken from an older source.

Checks passed LIBRARY_LINES_OVER_100=0 and TRANSPORT_ANALYSIS_SOURCE=0,
RATIONAL_RUNTIME_PASS and 200 Python tests in 8.715s.
Inventory passed 200 tests in 5.843s. The new downstream consumer/example,
umbrella, complete normal/slow lint and transitive axiom gates are not accepted:
the core build failure stopped that validation path.

Artifact metadata was inspected (not claimed as downloaded/extracted archives):
target 10950397582 (sha256 980361df472be862f9bbf768e06e9b080a37d612dcc2929e6179601b6fa29a9a),
global 10951490194 (sha256 f3023a67337fffd8ba0dc795ea738c9e2dd207e3982064a5e7e345cfedbebe32),
source 10949893660 (sha256 f586248913902df90e2ff1841f7a81bb9dc0884c376609060f495d43aa1e65c8).
CI and inventory exposed no artifacts. The checks snapshot job 108778284043 succeeded.

## Causes and combined repair

The original compressed information-state universe is `up`; full AOH
refinement uses `max (max ua uk) uq`. Although the public signals are the
same mathematically, the two universe-polymorphic publicTrace applications
were not definitionally interchangeable. The implicit signal parameter of
condition? was also inferred as the original model's signal carrier.

The repair explicitly selects fullInformation for condition? and for the
factual-child/native-state observation indices. A private induction on the
actual protocol trace proves that the refined public trace equals the original
public trace. The liveness proof uses that equality to apply the unchanged
PubliclyObservableTermination condition on the original game. Universes are
not collapsed to restrict the theorem, and no new semantic hypothesis is added.

The identifier `prefix` is a Lean syntax keyword. Its local binder and use
are renamed to `prefixLaw`. This also removes the cascading parser errors.

These are one combined core repair, with proof/type elaboration and spelling
changes only. Existing solver definitions, observations, mathematical intent,
workflow triggers, tests, target registrations and audit criteria are unchanged.
No new paper obligation is promoted.

## Original diagnostic block

```text
error: GameTheory/Analysis/ReBeL/CFRDStoredChild.lean:59:6: Type mismatch
  some (cfrDFactualChildBelief M trunk cut remaining obs possible)
has type
  Option (PublicBelief.{0, us, ua, uk, uq, max (max ua uk) uq} (fullInformation M).toInfoSignals obs)
but is expected to have type
  Option (PublicBelief.{0, us, ua, uk, uq, up} M.toInfoSignals obs)
error: GameTheory/Analysis/ReBeL/CFRDStoredChild.lean:62:6: Failed to rewrite using equation theorems for `PublicBelief.condition?`
error: GameTheory/Analysis/ReBeL/CFRDStoredChild.lean:85:55: Application type mismatch: The argument
  Eq.symm member.left
has type
  obs = publicTrace.{0, us, ua, uk, uq, max (max ua uk) uq} (fullInformation M).toInfoSignals first.trace
but is expected to have type
  obs = publicTrace.{0, us, ua, uk, uq, up} M.toInfoSignals first.trace
in the application
  Eq.trans same (Eq.symm member.left)
error: GameTheory/Analysis/ReBeL/CFRDStoredChild.lean:96:5: unexpected token 'prefix'; expected '_' or identifier
error: GameTheory/Analysis/ReBeL/CFRDStoredChild.lean:96:15: unexpected identifier; expected prec
error: GameTheory/Analysis/ReBeL/CFRDStoredChild.lean:107:16: unexpected identifier; expected ':'
error: GameTheory/Analysis/ReBeL/CFRDStoredChild.lean:181:4: Type mismatch
  some
    (cfrDFactualChildBelief M (cfrDComposedTrunk M fallback payoff cut remaining loss (fun {obs} ↦ solve) noise round)
      cut remaining (publicTrace M.toInfoSignals history.trace) possible)
has type
  Option
    (PublicBelief (fullInformation M).toInfoSignals (publicTrace.{0, us, ua, uk, uq, up} M.toInfoSignals history.trace))
but is expected to have type
  Option
    (PublicBelief (fullInformation M).toInfoSignals
      (publicTrace.{0, us, ua, uk, uq, max (max ua uk) uq} (fullInformation M).toInfoSignals
        (resolvedNextState (fullInformation M) state
              (cfrDDepthPlay (fullInformation M) (fullObservationClock M) (cfrDInformationFallback M fallback) payoff
                cut remaining (cfrDComposedOracle M fallback payoff cut remaining loss (fun {obs} ↦ solve) noise) round)
              cut history).history.trace))
```

## Revalidation boundary

The repaired source still needs all three separate required Actions workflows,
plus inventory, on its own SHA. Preserve 172 build targets, 134 targeted/276
global audit modules and 200 tests. Only the preceding 8bf7814 source has full
acceptance in M06-recursive-replay-8bf7814-accepted.md; that success cannot
validate this repair. M06 remains incomplete.
