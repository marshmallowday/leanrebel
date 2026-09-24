# M06 source rates: exact-source compiler repair

## Restart and inspected failure

Parent source: bd5cdaa304cb0791379c94fd0454ed28eabb683d.
Parent branch: rebel/m06-transport-rates-20260924 (preserved).
Continuation branch: rebel/m06-source-rates-repair-20260924.
All GitHub reads and writes use the ChatGPT GitHub plugin; no local Git or
alternative GitHub network path is used.

Independent ReBeL run35994227078/job107615561858 failed on 2026-09-24.
Its actual log compiles FinDistTransportRate and CFRDSourceRates, then reports
failures in Examples.CFRDSourceRates. The full gate consequently never reaches
successful supplemental lint and transitive axiom acceptance. Full CI35994227103
also failed. Snapshot job107615562354 passed. These are predecessor results,
not evidence that a repair has been accepted.

## Repair, with statements unchanged

1. Use the existing public FinDist.prob_pure_eq_ite lemma in concrete probability
   calculations. The previous simplifier knew self-mass but left off-diagonal
   probabilities unresolved, obstructing both conditional normalization and the
   rare-observation counterexample.
2. Rewrite expect_map and joint_defect before unfolding oldJoint, so the theorem
   matches the actual integrand rather than a prematurely unfolded source law.
3. Rewrite the OLD-support branch explicitly in disappearing_query before
   simplifying the absent NEW support. Retain the zero OLD-mass control.
4. Use add_le_add with le_rfl for the common parent budget, instead of the
   incorrectly oriented additive monotonicity lemma under the pinned toolchain.

No declaration statement, test, import, target, axiom audit, warning policy,
workflow, Lean/mathlib pin or coverage status is weakened or removed. The
positive-bias finite-time parent and its two fresh child solves remain intact.

## Semantic controls and scope

The OLD query has probability 1/100. Its NEW conditional changes maximally;
the joint atom variation and the OLD-weighted defect are both 1/50. An actual
opponent law concentrated on that supported query has defect 2 and density100.
The density-weighted source sum includes newly supported NEW atoms. Removing
the density would falsely predict a charge at most1/25. This is a counterexample
to that omitted premise, not a refutation of source Theorem3.

## Next exact checks

Read the continuation source SHA and its M06 targeted proof feedback, full CI,
independent ReBeL and inventory jobs. Read any annotations; retain failures and
repair them without dropping targets. Require compiler, normal/slow lint and
transitive public/private/generated declaration audit, with only propext,
Classical.choice and Quot.sound allowed. Record exact run/job IDs and counts
before accepting this slice. The current repair is unverified until then.

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
In particular, source-law bounds alone do not establish a uniform decaying rate
for arbitrary independently solved continuations, and native first-exit and
later carried-PBS re-solving obligations must not be assumed away.
