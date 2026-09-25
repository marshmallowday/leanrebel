# M06 joint retained-seed/type query slice

## Source and continuity

Branch: `rebel/m06-joint-query-20260925`.
Parent documentation checkpoint: `49b31047d55fb947953e95c160c571a3489dd067`.
Validated predecessor: `e65152038f6a9068be68aff28ad6845f74097e94`.
Read M06-native-gap-global-validation.md for the previously pending audit,
now inspected and passed. No predecessor proof is replayed or replaced.
Main remains at the accepted M05 checkpoint and is not advanced.

This is a project-level refinement of ROADMAP M06's random-iteration and
carried-belief obligation and M06-native-conditional-gap.md's explicit
product-law limitation. It is NOT a proof of the paper's full independent
re-solving guarantee. SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and
SAFE-THEOREM3 remain pending in coverage.json. M06 remains incomplete.
M06-joint-query-coverage.json records candidates, not acceptance transitions.

## Joint law, not a pair of marginal laws

Fix the canonical TypeBeliefSlice, its compatible conditional-history kernels,
the actual information-set CFR recurrence and a positive finite count t.
The same computed average opponents are used in every conditional Eq. (1)
best-response gap g(n,x). The native own policy at n is a legal information-local
policy; n is a private uniform index retained throughout continuation.

Let P(n,x) = iterationLaw(n) * ownTypeLaw(x). Existing native_mean_abs_le
establishes E_P |g| <= pbsRootCFRBound. For a possibly correlated ACTUAL law Q,
assume Q(n,x) = P(n,x) * r(n,x), with r <= C on P's support and C >= 0.
The ratio may depend on BOTH coordinates. It is analytical source-law data,
not information disclosed to an opponent or supplied to a solver policy.

pbsInformationCFR_joint_native_mean_abs_le proves E_Q |g| <= C * rootBound.
It uses the canonical informationReweight_expect, nonnegative absolute gap,
supported expectation monotonicity, product expectation and the already
proved actual native CFR bound. It assumes no small-gap conclusion for Q.
No minimum type mass or positive density on all joint atoms is required.
Density equality excludes new Q mass at an absent model type. Compatible
zero-mass conditional kernels remain defined and are not assigned false mass.

## Seed-dependent query kernel

pbsInformationCFR_seed_query_mean_abs_le starts with a kernel query(n).
It uses the actual tagged law

    iterationLaw.bind (fun n => query(n).map (fun x => (n,x))).

The density equality for this law is DERIVED from prob_bind_map_prod and
the per-seed identity query(n)(x) = ownTypeLaw(x) * r(n,x). The cap is checked
on model-supported types. No independence of query(n) and n is assumed.
This consumes an explicit kernel; it does not construct a carried posterior
from an arbitrary independent recursive solve or prove its density cap.

pbsInformationBudget_joint_native_mean_abs_le uses the actual positive
budget-computed CFR iteration count and gives E_Q |g| <= C * error.
There is no caller-supplied Nash witness or learner-convergence premise.
The finite-T residual is not dropped when an oracle happens to be exact.

All three declarations live under GameTheory.ReBeL in
GameTheory/Analysis/ReBeL/PBSJointNativeGap.lean.

## Controls and limitations

Examples.PBSJointNativeGap includes the live full-AOH HiddenTypes child at
budget 1/8, consuming the joint interface with the genuine uniform iteration
law and product own-type law (factor one). This is a formal solver instance,
not a numerical evaluation of the real-valued budget computation.

The finite-law diagonal query selects a uniform n in Fin 2 and then type=n.
Both marginals are uniform, exactly like the independent product, but the
nonnegative diagonal loss has mean 1 rather than 1/2. Its exact joint density
is 2 on the diagonal and 0 elsewhere. Thus the factor-two bound is sharp and
factor one cannot follow from equal marginals. A separate boundary proves
that a new type absent from a pure model law has no real density at all.
These are law-level positive/negative controls, NOT asserted to be actual
solver-generated CFR gaps. No changed-opponent conclusion is inferred.

Opponents, conditional kernels and the model PBS are fixed in this slice.
A law of queries correlated with the private seed is now expressible, but
deriving that law and quantitative cap for actual carried execution remains
open, as do changing-opponent/PBS native and late rates, first-exit support,
independent recursive re-solving safety and CarriedResolveStepBounds.

## Verification boundary

The new proof/control modules are appended to the analytic umbrella and M06
compiler target list. The targeted exact-leaf auditor is STRENGTHENED by
adding both native conditional-gap modules and both new joint-query modules
while preserving every existing module and its normal/slow lint and axiom
checks. The independent all-ReBeL auditor and full-repository CI are unchanged.
No trust allowance, dependency pin, negative control or warning gate is removed.

At this implementation checkpoint new-source Lean compilation, lint and
transitive-axiom evidence are pending its GitHub Actions. The predecessor's
successful 247-module audit is not reused as new-source validation. Inspect
actual target-SHA output before accepting these candidates. No local Lean
compiler execution is claimed.
