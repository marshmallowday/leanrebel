# M06 actual finite-iteration and private-seed controls

Continue from `rebel/m06-recovery`, preserving the parent checkpoint
0245b29e0285f7b29f4b8e85e22909ce73a5d799. That exact source passed targeted
run 35466256006 and inventory run 35466256007. Its full ReBeL run 35466256005
and repository CI 35466256014 were in progress at the last observation.

## Distinct finite-T controls

`Examples/CFRDExecution.lean` runs the actual coupled depth-limited driver
on the existing two-stage HiddenTypes protocol. Its exact reference oracle
satisfies zero value error; zero remaining fuel derives the continuation
contract. At T=1 the actual averaged profile equals the declared pure fallback,
and a legal information-local player-one deviation gains exactly 2. The same
solver satisfies its nonzero finite-time bound at every positive T. This
pure fallback is NOT relabeled as the source's uniform initialization.

`Examples/CFRDUniformControl.lean` separately treats the paper's no-warm-start,
uniform, pre-update T=1 convention in its established Figure 1 modified-RPS
game. Canonical full-AOH execution realizes independent uniform moves, worth
zero to player zero. An actual unilateral rock deviation yields 1/3. Thus
zero numerical/continuation error at finite T does not imply exact Nash,
and an all-delta deviation bound is false for any constants. This is a
protocol-level source control, not merely the M01 symbolic recurrence.

Source locators: published main paper Figure 1 and Theorem 3; supplement
Algorithm 2 (initialization, sampled pre-update policy), Appendix G Lemma 5
and Theorem 3. The printed all-delta statement and the additive finite-T
proof pattern remain separate. No claim about successful neural training,
warm-start variants, or a full C++ implementation equivalence is inferred.

## Seed and averaging control

`Examples/CFRDSeedControl.lean` uses an actual two-stage hidden-type history
whose focal first and second actions differ. Under either privately selected
complete bit policy its probability is zero. Under fresh per-information-state
mixing it is 1/16 (including the real hidden chance draw). The carried-state
execution is therefore NOT the coordinate-average execution. The arbitrary
opponent is fixed outside the private seed, and policy legality uses the
existing canonical choices and information model throughout.

## Validation and scope

All fourteen targeted roots pass the offline pinned Lean 4.33.1 compiler
with library warning/error flags. The inventory structural check and all 76
Python adversarial fixtures pass locally. New examples are explicit umbrella
imports and targeted roots, and remain in recursive lint/axiom enumeration.
Exact-SHA Actions is still authoritative for full acceptance.

This checkpoint does not complete recursive test-time re-solving or discharge
all local continuation contracts from a constructed leaf solver. Do not mark
M06 complete or silently promote the complete Theorem 3 coverage family.
