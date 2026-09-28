# Stored-child consumer signal-index failure at 99cfe59

Source 99cfe593f08280a6f0eb791c44319ff8a42df43f on
rebel/m06-kernel-value-repair-20260927 was re-read before repair.
Plugin identity marshmallowday has admin/push access. Default main remains
6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098. Continue this unfinished M06 branch;
no main commit, PR or force push is involved.

## Exact-source Actions

| Workflow | Run / job | Result |
| --- | --- | --- |
| CI | [36386358269](https://github.com/marshmallowday/leanrebel/actions/runs/36386358269) / 108812455311 | build failed |
| ReBeL checks | [36386358240](https://github.com/marshmallowday/leanrebel/actions/runs/36386358240) / 108812455291 | build failed |
| M06 targeted | [36386358259](https://github.com/marshmallowday/leanrebel/actions/runs/36386358259) / 108812455475 | build failed |
| Source inventory | [36386358235](https://github.com/marshmallowday/leanrebel/actions/runs/36386358235) / 108812455748 | success |

Every head SHA matches. Complete decoded logs show the same six type
diagnostics in the three compiler jobs. Explicit PBSChildSolve/trunk types
removed the previous three deterministic timeouts. CFRDStoredChild still
compiles in all three jobs (3.9s / 3.8s / 3.3s).

Checks passed LIBRARY_LINES_OVER_100=0, TRANSPORT_ANALYSIS_SOURCE=0,
RATIONAL_RUNTIME_PASS and 200 Python tests in 9.281s.
Inventory passed 200 tests in 9.714s. The consumer/example and complete
normal/slow lint/transitive axiom validation are still not accepted.

Artifact metadata was inspected, not claimed as extracted archives:
target 10954941796, sha256 6120fe5d7151a88872cc67b194663bb524d1252c7d8bd5f9608056b7ca0eb76f;
global 10955248207, sha256 564fbb40846eb14664a096261c717b1cd71c640d9b2630e41d6c84d57e29ab43;
source 10954183913, sha256 284ead5196183a5dbd68b74dc883f9c8058a74fce12cdf6af4f4ca21502e16e7.
Snapshot job 108812455528 succeeded; CI and inventory list no artifacts.

## Cause and combined repair

The consumers still indexed their factual child and resolver query with
publicTrace M.toInfoSignals, while next.belief and the repaired core theorem
use publicTrace (fullInformation M).toInfoSignals. Equal mathematical public
observations are not definitionally interchangeable when their signal
structures differ, even with the uniform universe used in this module.

Use the full-information public trace consistently for all consumer possible,
supported-child, stored-state and resolver-query indices. Apply the same
change in both concrete consumers, using the existing model fullPrior signal
structure. Their generic storedPublic_head / public-termination proofs remain
on the original signals and are unchanged.

The original public signal fields are preserved by fullInformation; no
observation, solver input or semantic condition is added. Existing core proof,
recursive computation, budgets, typed solver aliases, all tests, workflow,
172 targets and 134/276 audit modules are unchanged. No heartbeat limit or
audit threshold is changed. This repair plus evidence is one commit.

## Full compiler diagnostic block

```text
error: GameTheory/Analysis/ReBeL/PBSStoredChildReplay.lean:55:18: Type mismatch
  some child
has type
  Option (PublicBelief (fullInformation M).toInfoSignals (publicTrace M.toInfoSignals history.trace))
but is expected to have type
  Option
    (PublicBelief (fullInformation M).toInfoSignals (publicTrace (fullInformation M).toInfoSignals next.history.trace))
error: GameTheory/Analysis/ReBeL/PBSStoredChildReplay.lean:58:52: Application type mismatch: The argument
  next.belief
has type
  Option
    (PublicBelief (fullInformation M).toInfoSignals (publicTrace (fullInformation M).toInfoSignals next.history.trace))
but is expected to have type
  Option (PublicBelief (fullInformation M).toInfoSignals (publicTrace M.toInfoSignals history.trace))
in the application
  pbsRecursiveDepthResolver recursiveNoise cuts M fallback payoff bound (child.law.positiveMassFloor * loss) plays
    next.iteration (publicTrace M.toInfoSignals history.trace) next.belief
error: GameTheory/Analysis/ReBeL/PBSStoredChildReplay.lean:62:28: Type mismatch
  some child
has type
  Option (PublicBelief (fullInformation M).toInfoSignals (publicTrace M.toInfoSignals history.trace))
but is expected to have type
  Option
    (PublicBelief (fullInformation M).toInfoSignals (publicTrace (fullInformation M).toInfoSignals next.history.trace))
error: GameTheory/Analysis/ReBeL/PBSStoredChildReplay.lean:64:53: Application type mismatch: The argument
  possible
has type
  CFRDFactualChildPossible M
    (cfrDComposedTrunk M fallback payoff cut remaining loss
      (fun {obs} ↦ pbsRecursiveDepth recursiveNoise cuts E M fallback payoff bound) noise round)
    cut remaining (publicTrace M.toInfoSignals history.trace)
but is expected to have type
  CFRDFactualChildPossible M (cfrDComposedTrunk M fallback payoff cut remaining loss (fun {obs} ↦ solve) noise round)
    cut remaining (publicTrace (fullInformation M).toInfoSignals history.trace)
in the application
  cfrDComposedRound_storedChild M observable fallback payoff cut remaining loss (fun {obs} ↦ solve) noise round state
    prior stored initial history possible
error: GameTheory/Analysis/ReBeL/PBSStoredChildReplay.lean:102:50: Application type mismatch: The argument
  next.belief
has type
  Option
    (PublicBelief (fullInformation M).toInfoSignals (publicTrace (fullInformation M).toInfoSignals next.history.trace))
but is expected to have type
  Option (PublicBelief (fullInformation M).toInfoSignals (publicTrace M.toInfoSignals history.trace))
in the application
  pbsRecursiveDepthResolver recursiveNoise cuts M fallback payoff bound (child.law.positiveMassFloor * loss) plays
    next.iteration (publicTrace M.toInfoSignals history.trace) next.belief
error: GameTheory/Analysis/ReBeL/PBSStoredChildReplay.lean:148:50: Application type mismatch: The argument
  next.belief
has type
  Option
    (PublicBelief (fullInformation M).toInfoSignals (publicTrace (fullInformation M).toInfoSignals next.history.trace))
but is expected to have type
  Option (PublicBelief (fullInformation M).toInfoSignals (publicTrace M.toInfoSignals history.trace))
in the application
  pbsRecursiveDepthResolver recursiveNoise cuts M fallback payoff bound (child.law.positiveMassFloor * loss) plays
    next.iteration (publicTrace M.toInfoSignals history.trace) next.belief
```

Repaired-source full validation remains pending on its own SHA. No local
Lean/Python execution is claimed. The 8bf7814 full acceptance is historical
evidence only. M06 remains incomplete.
