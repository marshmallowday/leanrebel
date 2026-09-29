# Cross-query value candidate 29b27d4: two example type mismatches

Exact candidate: `29b27d475d96e67c46914d1b6e902e5baf71a03c`.
Branch: `rebel/m06-kernel-value-repair-20260927`.
Latest accepted dependency remains `ffab72bcee96bd262a0a1c5f3966a5e96b41aed7`.
M06 and this candidate's full validation are incomplete.

## Exact Actions evidence

| Run | Job | Result |
| --- | --- | --- |
| [CI36505835454](https://github.com/marshmallowday/leanrebel/actions/runs/36505835454) | 109206960343 | failure |
| [checks36505835263](https://github.com/marshmallowday/leanrebel/actions/runs/36505835263) | 109206959496 | failure |
| source snapshot in checks | 109206959230 | success |
| [target36505835377](https://github.com/marshmallowday/leanrebel/actions/runs/36505835377) | 109206959849 | failure |
| [inventory36505835389](https://github.com/marshmallowday/leanrebel/actions/runs/36505835389) | 109206960177 | success |

Complete decoded job logs were obtained for all four principal jobs. The three
compiler logs contain exactly the same two source diagnostics reproduced below.
All three have zero axiom records: full lint/axiom validation was not reached.

PBSRecursiveValueStability compiled in CI/checks/target in3.1/3.8/3.6s.
CFRDStoredSolveValue compiled in2.6/2.4/2.5s. Their example module failed.
No whole-library build/lint acceptance is inferred from those successes.
Checks reports LIBRARY_LINES_OVER_100=0, TRANSPORT_ANALYSIS_SOURCE=0,
RATIONAL_RUNTIME_PASS, and240 Python tests in9.879s. Inventory independently
reports240 tests in6.481s. These results belong to29b27d4 only.

Artifact metadata was read, but ZIP bytes were not read. CI/inventory have
no artifact. Evidence comes from complete decoded logs, not inferred ZIP content.

| ID | Name | Bytes | Digest |
| --- | --- | --- | --- |
| 11008280470 | rebel-validation-29b27d475d96e67c46914d1b6e902e5baf71a03c | 21447 | sha256:b3fec09251caf235cd1b2c88abeba5491d21bcdc98fbcbc0247c3e85fc097e44 |
| 11007345431 | rebel-source-29b27d475d96e67c46914d1b6e902e5baf71a03c | 2982348 | sha256:4f9a35e680cf81b0b079fccf35e06b597f477c60a40fe22b8d61373cc7a5c508 |
| 11007615872 | m06-targeted-29b27d475d96e67c46914d1b6e902e5baf71a03c | 5128 | sha256:b6e0c34747c21a9b991662ff2b7b17aaf0cce7d84126f8004aa81cc3d81ca2ee |

## Repair and static type review

Both failures occur at the final `simpa only` of
crossQuery_partition_value and crossQuery_partition_private. The simplified
estimate still prints pbsRecursiveDepth versus recursiveInitialProfile,
fullInformation(reducedModel) versus model, and list sums versus numeral3.
The restricted simplification did not establish the required final type match.

Both consumers now first eliminate local lets with `dsimp only at estimate`,
rewrite atomVariation_self/mul_zero/add_zero in that estimate, and pass it
with `exact estimate`. Ordinary definitional type checking may unfold the
existing profile/model aliases and numeral list sums. No equality between
different solvers is assumed. No simplifier expansion through the recursive
algorithm is requested. New Actions must establish that this repair suffices.

The actual recursiveInitialProfile definition is the same [1,1,1] solve with
the same reducedModel/fallback/payoff/bound/belief/tolerance. The model alias
is explicitly reducible to fullInformation(reducedModel). Both list sums are3.
The already accepted recursiveInitial_isNash and potentialSecurity_private_root
consume these same aliases directly. The new generic three solver helpers,
stored-public/live-child theorem, and all three examples were reread.
State-dependent PBS indices, full signal carrier, universes, action/history/
InfoState instances, argument order, both error coefficients and seed-blind
unknown opponent agree. The stored noisy example already uses the successful
rewrite-then-exact pattern and receives no unnecessary change.

Reversing these two proof replacements reproduces the entire parent example
file byte for byte. All definitions, theorem signatures, other proofs, local
instances, mathematical assumptions, tests, registrations, workflow/audit
settings and heartbeat limits remain unchanged. Longest example line is97
UTF-16 code units. The previous static review overestimated what simpa only
would unfold at the final consumer boundary. This static review is not Lean
compiler success; all exact-new-SHA gates remain required.

## Complete common compiler diagnostics

```text
error: GameTheory/Analysis/ReBeL/Examples/PBSRecursiveValueStability.lean:53:2: Type mismatch: After simplification, term
  estimate
 has type
  @LE.le ℝ Real.instLE
    |(recursiveInitialBelief.law.bind
              ((fullInformation (reducedModel fullPrior)).runBehavioralFrom
                (pbsRecursiveDepth pbsRecursiveAllocatedNoise [1, 1, 1] (protocol fullPrior) (reducedModel fullPrior)
                  pbsRootControlFallback cfrPayoff 2 recursiveInitialBelief (1 / 8))
                [1, 1, 1].sum)).expect
          (cfrPayoff who) -
        (recursiveInitialBelief.law.bind
              ((fullInformation (reducedModel fullPrior)).runBehavioralFrom
                (pbsRecursiveDepth pbsRecursiveAllocatedNoise [3] (protocol fullPrior) (reducedModel fullPrior)
                  pbsRootControlFallback cfrPayoff 2 recursiveInitialBelief (1 / 4))
                [3].sum)).expect
          (cfrPayoff who)|
    (1 / 8 + 1 / 4)
but is expected to have type
  @LE.le ℝ Real.instLE
    |(recursiveInitialBelief.law.bind ((model fullPrior).runBehavioralFrom (recursiveInitialProfile (1 / 8)) 3)).expect
          (cfrPayoff who) -
        (recursiveInitialBelief.law.bind ((model fullPrior).runBehavioralFrom second 3)).expect (cfrPayoff who)|
    (1 / 8 + 1 / 4)

error: GameTheory/Analysis/ReBeL/Examples/PBSRecursiveValueStability.lean:74:2: Type mismatch: After simplification, term
  estimate
 has type
  @LE.le ℝ Real.instLE
    ((recursiveInitialBelief.law.bind
            ((fullInformation (reducedModel fullPrior)).runBehavioralFrom
              (pbsRecursiveDepth pbsRecursiveAllocatedNoise [1, 1, 1] (protocol fullPrior) (reducedModel fullPrior)
                pbsRootControlFallback cfrPayoff 2 recursiveInitialBelief (1 / 8))
              [1, 1, 1].sum)).expect
        (cfrPayoff who) -
      (1 / 8 + 2 * (1 / 4)))
    ((pbsRecursiveDepthDraw pbsRecursiveAllocatedNoise [3] (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
          recursiveInitialBelief (1 / 4)).expect
      fun chosen ↦
      (recursiveInitialBelief.law.bind
            ((fullInformation (reducedModel fullPrior)).runBehavioralFrom (unknown.update who (chosen who))
              [3].sum)).expect
        (cfrPayoff who))
but is expected to have type
  @LE.le ℝ Real.instLE
    ((recursiveInitialBelief.law.bind ((model fullPrior).runBehavioralFrom (recursiveInitialProfile (1 / 8)) 3)).expect
        (cfrPayoff who) -
      (1 / 8 + 2 * (1 / 4)))
    ((pbsRecursiveDepthDraw pbsRecursiveAllocatedNoise [3] (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
          recursiveInitialBelief (1 / 4)).expect
      fun chosen ↦
      (recursiveInitialBelief.law.bind ((model fullPrior).runBehavioralFrom (unknown.update who (chosen who)) 3)).expect
        (cfrPayoff who))
```

Scalar value stability remains distinct from policy/kernel or typewise vector
identity, internal-rooted/fresh-original computation correspondence, and a
full native small-rate guarantee. No source obligation is promoted.
