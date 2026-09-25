# M06 same-PBS scalar stability — semantic review

## Identity and scope

This is a project lemma for the M06 source-rate investigation. Its source is
5a9fc55e6b944abb16ec7f2e16e80deb0db341f3; exact validation belongs in
M06-scalar-stability-evidence.md. It does not claim to prove the paper's
Theorem3 or to complete M06.

The canonical continuation game, payoff, horizon and JOINT public belief are
held fixed. The compared objects are two computed reach-weighted CFR outputs.
They are not two individual native iterations, separately redrawn private
seeds, a tuple of private marginal beliefs, or two later carried posteriors.

## The seven theorem interfaces

All names below are in GameTheory.ReBeL, defined in
GameTheory/Analysis/ReBeL/PBSValueStability.lean.

1. approxNash_value_sub_le compares arbitrary approximate Nash profiles in one
   canonical two-player zero-sum GameForm. Each Nash certificate quantifies
   over every strategy in that form. No exact equilibrium witness is assumed.
2. approxNash_value_abs_sub_le reverses the profiles to bound the absolute
   difference by the SUM of their two unilateral improvement allowances.
3. pbsInformationCFR_value_abs_sub_le discharges the certificates using actual
   information-set CFR at two positive iteration counts, in the original
   behavioral continuation game. It retains both finite-time residuals.
4. pbsInformationBudgetProfile_value_abs_sub_le compares two actual finite
   child solves at independently requested positive budgets. The counts come
   from the existing budget function; the caller supplies no Nash witness.
5. pbsInformationAllocatedDepthProfile_value_abs_sub_le compares two existing
   allocated noisy depth-limited solves. The two numerical predictors may
   differ but each must meet its own explicit allocation bound. This is not
   a proof that a trained network satisfies that numerical contract.
6. pbsInformationBudgetRounds_error_of_le proves the requested residual bound
   for EVERY count at or above the computed budget, not only at one count.
7. pbsInformationCFR_late_value_abs_sub_le combines the two actual residuals
   with an explicit half-tolerance cutoff, uniformly over both later counts
   and both legal fallback policies, at the same public belief.

## Cross-profile proof

Let U denote player0's expected utility. For profiles p and q let c=(p0,q1).
Player1's approximate Nash inequality at p and zero-sum identity give

    U(p) <= U(c) + error_p.

Player0's approximate Nash inequality at q gives

    U(c) <= U(q) + error_q.

Adding yields U(p)-U(q)<=error_p+error_q. Swapping p and q yields the
absolute bound. The proof uses the existing Profile.update and IsNash, not
an alternative game, probability, or equilibrium abstraction. The two errors
are not silently replaced by zero. The same-game and zero-sum premises are
substantive; independent exact-rational negative controls exercise both.

## Explicit late-output cutoff

Fix the common belief b, payoff bounds B and horizon H. Define

    C = pbsRootCFRBound M b.law B H 1,
    N(tolerance) = floor((abs(C)/(tolerance/2))^2) + 1.

For tolerance>0, N is positive. The existing exact factorization gives the
residual at t as C*sqrt(t)/t. For every t>=N, the floor inequality implies
abs(C)^2 <= t*(tolerance/2)^2. Nonnegative square roots and the strictly
positive denominator then bound the residual by tolerance/2. Applying this
to both T and S proves

    T,S >= N(tolerance)  ==>  abs(V_T - V_S) <= tolerance.

The coefficient C is independent of the fallback policy. Therefore the two
fallbacks may differ without changing this cutoff. If C=0 the cutoff remains
1; no zero-length averaging or division by zero is smuggled into the proof.
This gives a quantitative scalar Cauchy estimate for the family of outputs,
not a convergence theorem for individual CFR strategies or a value vector.

## Solver assumptions and trust boundary

The solver-facing theorems retain finite legal histories, finite action types,
a total legal fallback policy, the canonical full action-observation model,
two players, pointwise zero-sum payoffs, and explicit global payoff magnitude
bounds. Fixed-count theorems require positive counts. Budget and allocation
statements require strictly positive requested accuracies. The depth theorem
retains both numerical-noise bounds and does not identify model beliefs with
actual execution posteriors. The downstream decode theorem covers every
original behavioral deviation, not just an enumerated subset of plans.

These are noncomputable real-valued Lean specifications of a finite algorithm.
They do not certify C++/Python, floating-point execution, or a neural predictor.
Fraction-based regression tests are supplementary and are not kernel proofs.

## Positive and hostile controls

The HiddenTypes example retains the existing nontrivial public-belief game
and legal-history enumeration, including factually absent histories. The
first consumer compares actual finite budget solves at1/4 and1/8 and bounds
their scalar difference by3/8. The second consumer quantifies over arbitrary
counts beyond the explicit1/8-tolerance cutoff for actual CFR outputs.

The hostile chance game has old law delta_0 and fresh law giving equal mass
to payoff-1 and payoff+1. Both means are zero. In its canonical zero-sum
GameForm every legal profile is exact Nash; the column still has its full
legal menu. A valid coupling exists. For EVERY coupling with the correct
marginals, the old coordinate is0 on support, so the expected positive payoff
change is exactly1/2. No coupling can satisfy a directed-cost bound below1/2.
This is a sharp counterexample to deducing small directed cost from scalar
Nash accuracy, not a counterexample to ReBeL's original safety claim.

## Obligations deliberately not discharged

A scalar root estimate is not a uniform information-fiber estimate and does
not compare values after the belief changes. Supported conditional vector
bounds, native-iteration first-exit rates, later independent carried-PBS
re-solving and CarriedResolveStepBounds still require their own source proofs.
The existing actual private seed/history law and unknown-opponent weighting
cannot be replaced by independent resampling or by an assumed root inequality.

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
Preserve finite-T residuals at zero oracle error and distinguish the printed
Theorem3 from the separately tracked corrected reading.
