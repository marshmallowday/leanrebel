# M06 same-PBS scalar stability — compiler checkpoint

## Provenance and scope

Base documentation checkpoint: 2e1de273b9164743decdd8a283b3249f34bf5600.
Resumption commit: 4ddb211c018100011c31407b3ed90a0aa67e4164.
Branch: rebel/m06-scalar-stability-20260925.
The prior uncommitted candidate ZIP SHA256 is
951ba0b3bd41500c866c63e711c59fd4c613c032b9e7d1c47089c12e3746b729.
Its Lean and Python candidates were checked against the original file hashes
before restoration. No stale snapshot was used to replace checkpoint docs.

This is a PROJECT lemma serving the M06 source-rate investigation, not the
paper's unmodified Theorem3 or a native-iteration guarantee. All four canonical
M06 parent rows retain pending status. The scoped companion tracks this slice.

## Mathematical review

Let p and q be approximate Nash profiles of the same canonical two-player
zero-sum game, with unilateral allowances e_p and e_q. Set c=(p_0,q_1).
Player1's inequality at p gives U(p)<=U(c)+e_p; player0's inequality at q gives
U(c)<=U(q)+e_q. Therefore U(p)-U(q)<=e_p+e_q. Reverse the profiles to get the
absolute-value bound. No exact equilibrium witness or strategy/law equality
is required. The proof uses the existing Profile.update, IsNash,
euPreferenceWithin, expectedUtility, and zero-sum expectation identities.

The solver-facing declarations discharge the Nash premises with existing
pbsInformationCFR_isNash, pbsInformationBudgetProfile_isNash, and
pbsInformationAllocatedDepthProfile_isNash. They retain the common joint PBS,
common game/horizon/payoff, finite histories/actions, positive iteration counts
or budgets, payoff bounds, and the two explicit numerical-noise contracts.
Fallbacks, counts, requested budgets and noise predictors may differ.
Outputs are the existing reach-weighted solver outputs, not native iterates.

The positive HiddenTypes consumer uses actual finite child solves with budgets
1/4 and 1/8 and scalar bound3/8. The negative canonical zero-sum chance game
compares delta_0 with a fair spread on values-1 and+1. Every profile is exact
Nash and both means are zero. Every valid coupling costs1/2 because the old
marginal is pure. Existence of a valid coupling is also proved, avoiding a
vacuous negative test. This refutes neither ReBeL nor conditional value claims;
it prevents using scalar Nash accuracy to fabricate a small coupling cost.

## Validation at source checkpoint

The two Lean files still require exact-SHA compiler, lint and transitive-axiom
inspection. No build or axiom success is claimed by this source commit.
Static integration retains134 old targets and96 old supplemental audit modules,
adding2 to each. The existing umbrella imports are retained with2 additions.
No workflow, dependency, axiom allowance or old adversarial control changes.

Offline commands rerun in this continuation:

    python scripts/rebel/check_coverage.py
    python scripts/rebel/check_inventory.py
    python -W error -m unittest discover -s scripts/rebel/tests -v

Structural checks passed; all82 tests passed, including6 new exact-Fraction
controls. The new enumeration checks6561 two-by-two game/profile-pair cases.
These checks are numerical regression evidence, not general Lean proof.

A duplicate umbrella import introduced while transcribing a blob was detected
by mismatch with the expected blob SHA and corrected BEFORE commit. The
published umbrella blob matches the restored candidate exactly. This source
checkpoint contains no duplicate from that transcription.

## Remaining work

Read this source commit's M06 target, full CI, independent ReBeL and inventory
runs. Preserve actual failures and focused fixes in later commits. Then record
the exact success SHA, run/job IDs, log hashes and per-declaration axiom output.
Native/late-training conditional value rates, native first-exit, later carried
PBS re-solving and CarriedResolveStepBounds remain independent obligations.
